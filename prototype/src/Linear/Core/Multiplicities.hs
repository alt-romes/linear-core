{-# LANGUAGE GHC2021, DerivingVia, GeneralizedNewtypeDeriving, LambdaCase, UnicodeSyntax, ScopedTypeVariables, ViewPatterns #-}
module Linear.Core.Multiplicities where

import Control.Monad.Except
import Data.Function
import GHC.Core.Map.Type (deBruijnize)
import GHC.Core.Multiplicity (scaledMult)
import GHC.Types.Var
import GHC.Utils.Outputable
import qualified Data.List as L
import qualified GHC.Core.TyCon as C
import qualified GHC.Core.Multiplicity as C
import qualified GHC.Core.Type as C
import qualified GHC.Plugins
import Data.Bifunctor
import Data.Maybe
import GHC.Prelude (pprTrace, pprTraceM)
import qualified GHC.Core.TyCo.Rep as C
import qualified GHC.Core.DataCon as C
import qualified Data.Map as M
import GHC.Core.Type (isMultiplicityVar, isMultiplicityTy)

--------------------------------------------------------------------------------
----- Id Binding ---------------------------------------------------------------
--------------------------------------------------------------------------------

data BindSite = LetBinder | LetRecBinder | LetRecBinderDry | LambdaBinder | CaseBinder | PatternBinder
  deriving (Show, Eq)

data IdBinding = LambdaBound Mult    -- lambdas
               | DeltaBound UsageEnv -- both let and case binders (including pattern variables)
               deriving Eq

isBindingLinear :: IdBinding -> Bool
isBindingLinear (LambdaBound m) = isLinear m
isBindingLinear (DeltaBound  _) = False

--------------------------------------------------------------------------------
----- Multiplicities -----------------------------------------------------------
--------------------------------------------------------------------------------

data Mult = Relevant C.Mult
          | Irrelevant C.Mult
          | Tagged Tag Mult

data Tag = Tag GHC.Plugins.DataCon Int

-- | When using a linear resource, we must check whether the resource is
-- irrelevant or relevant. We can't consume irrelevant resources directly (as
-- though they existed), we can only consume irrelevant resources by consuming a
-- usage environment that mentions the irrelevant resource.
--
-- In this sense, this hidden option is always "DisallowIrrelevant" except for
-- when we're 'use'ing a $\Delta$-bound variable, in which case we internally
-- switch to "AllowIrrelevant" since we know the variable being used is coming
-- from a usage environment.
data AllowIrrelevant = DisallowIrrelevant | AllowIrrelevant deriving (Eq, Show)

-- ROMES:TODO: This is an incorrect instance of equality for mults because of mult. vars.
instance Eq Mult where
  Relevant m1 == Relevant m2 = deBruijnize m1 == deBruijnize m2
  Irrelevant m1 == Irrelevant m2 = deBruijnize m1 == deBruijnize m2
  Tagged t1 m1 == Tagged t2 m2 = t1 == t2 && m1 == m2
  _ == _ = False

instance Eq Tag where
  Tag c1 i1 == Tag c2 i2 = c1 == c2 && i1 == i2

isLinear :: Mult -> Bool
isLinear = not . isUnrestricted

isUnrestricted :: Mult -> Bool
isUnrestricted (Relevant m)   = C.isManyTy m
isUnrestricted (Irrelevant m) = C.isManyTy m
isUnrestricted (Tagged _ m)   = isUnrestricted m

isIrrelevant :: Mult -> Bool
isIrrelevant (Relevant _)   = False
isIrrelevant (Irrelevant _) = True
isIrrelevant (Tagged _ m)   = isIrrelevant m

-- Create a multiplicity map from datacon and type of value using that datatype
-- The map can then be used to lookup multiplicities of the dataConOrigArgTys
--
-- INVARIANT: DataCon constructs value of given type
-- Returns the [Scaled Type] of dataConOrigArgTys, but the mults of each arg
-- are instanced by the corresponding type parameter of the datatype
uniDataConOrigArgTys :: C.DataCon -> C.Type -> [C.Scaled C.Type]
uniDataConOrigArgTys con ty
  | C.TyConApp _ args <- ty
  =
    let mapmult :: M.Map Var C.Mult
        mapmult = M.fromList $ zip (C.dataConUnivTyVars con) args
        res = L.map (\case
                        C.Scaled m t
                          | C.TyVarTy mtv <- m
                          -> C.Scaled (fromMaybe m (M.lookup mtv mapmult)) t
                          | otherwise -> C.Scaled m t
                    ) (C.dataConOrigArgTys con)
     in -- pprTrace "uniDataConOrigArgTys" (ppr con <+> ppr ty <+> ppr (C.dataConUnivTyVars con) <+> ppr (zip (filter isMultiplicityVar (C.dataConUnivTyVars con)) (filter isMultiplicityTy args)) <+> ppr args <+> ppr mapmult <+> ppr res)
        res
  | otherwise = C.dataConOrigArgTys con

data Usage = Zero | LCM Mult

-- | Extract all tags of a multiplicity, left to right
--
-- > extractTags 1#(,)_1#Pair_1#K_1 = [(,)_1, Pair_1, K_1]
extractTags :: Mult -> [Tag]
extractTags = reverse . go where go (Tagged t m) = t:go m
                                 go _ = []

removeTag :: Mult -> Mult
removeTag (Tagged _ m) = removeTag m
removeTag m = m

-- | Split a resource as needed given a tagstack then consume the resource
-- specified by the tag.
--
-- Returns the resource fragments that were split as needed, except for the
-- fragment that was consumed, and the fragment that was consumed.
-- (Returns ([],_) if the last resource was consumed)
--
-- Irrelevant-ness of the multiplicities (both input and output) must be
-- handled outside of this function, here they are split just like relevant ones
splitAsNeededThenConsume :: ∀ m. MonadError String m
                         => AllowIrrelevant -> [Tag] -> Mult -> m ([Mult], Mult)
splitAsNeededThenConsume ir ts' m'' = do
  res <- second fromJust <$> splitAsNeededThenConsume' ir ts' m''
  -- pprTraceM "splitAsNeededThenConsume input:" (ppr ts' <+> ppr m'')
  -- pprTraceM "splitAsNeededThenConsume out:" (ppr res)
  return res
    where
  splitAsNeededThenConsume' :: MonadError String m
                           => AllowIrrelevant -> [Tag] -> Mult -> m ([Mult], Maybe Mult)
  -- If there is no tag left then this is the resource we are looking for, so we
  -- consume it. We know this is the resource we need because we only recurse
  -- after splitting on the index we're looking for. If it's the last tag we're
  -- done, otherwise we keep splitting.
  splitAsNeededThenConsume' allowsIrrelevant [] m
    | DisallowIrrelevant <- allowsIrrelevant
    , isIrrelevant m = throwError "Tried to use an irrelevant result when not allowed"
    | otherwise = pure ([], Just m)

  splitAsNeededThenConsume' allowsIrrelevant tagstack m
    | DisallowIrrelevant <- allowsIrrelevant
    , isIrrelevant m = throwError "Tried to use an irrelevant result when not allowed"

    | extractTags m == tagstack
    = pure ([], Just m) -- consume successfully since the mult tags matches exactly the tagstack

  splitAsNeededThenConsume' allowsIrrelevant (Tag con i:ts) m@(extractTags -> Tag con' i':_)
    | con == con' && i == i'
    = splitAsNeededThenConsume' allowsIrrelevant ts m

  splitAsNeededThenConsume' allowsIrrelevant (Tag con i:ts) m
    =
      let res :: m [([Mult], Maybe Mult)]
          res = traverse @_ @_ @Mult @([Mult], Maybe Mult) (\case
                   m'@(Tagged (Tag _ i') _)
                      -- From the resources we split, this has the index we are
                      -- looking for, so we keep splitting inside
                      | i' == i -> splitAsNeededThenConsume' allowsIrrelevant ts m'

                      -- Otherwise, the resource we need isn't down this path, so
                      -- we can stop splitting here
                      | otherwise -> pure ([m'], Nothing)
                   _ -> error "impossible, splitResourceAt guarantees returned resource is tagged"
                )
                (splitResourceAt con m)
       in foldl (\(acc_ms, acc_consumed) (splits, m_consumed) ->
                    (acc_ms Prelude.<> splits, case (acc_consumed, m_consumed) of
                      (Nothing, Nothing) -> Nothing
                      (Just cm, Nothing) -> Just cm
                      (Nothing, Just cm) -> Just cm
                      (Just  _, Just  _) -> error "Bolas! More than one fragment consumed while splitting and consuming!"
                    )
                ) ([], Nothing) <$> res

-- | Splits a resource according to a constructor's number of linear fields
splitResourceAt :: GHC.Plugins.DataCon -> Mult -> [Mult]
splitResourceAt con mult = map (\i -> Tagged (Tag con i) mult) [1..numberOfLinearFields con]

-- | Splits a resource at a tagstack, basically generating a fragment matching
-- each tag, (recursively) splitting as many times as necessary
splitResourceAtTagStack :: [Tag] -> Mult -> [Mult]
splitResourceAtTagStack []     m    = [m]
splitResourceAtTagStack (Tag c i:ts) mult = do
  let res = splitResourceAt c mult
   in concatMap (\(m', i') -> if i == i' then splitResourceAtTagStack ts m' else [m']) (zip res [1..])

numberOfLinearFields :: GHC.Plugins.DataCon -> Int
numberOfLinearFields = length . filter (not . GHC.Plugins.isManyTy . scaledMult) . GHC.Plugins.dataConOrigArgTys

-- Returns True when all constructors of this datatype have 0 linear components
allConstructorsAreUnrestricted :: C.Type -> Bool
allConstructorsAreUnrestricted (C.TyConApp tc _) = all ((== 0) . numberOfLinearFields) $ C.tyConDataCons tc
allConstructorsAreUnrestricted _ = False

--------------------------------------------------------------------------------
----- Usage Environments -------------------------------------------------------
--------------------------------------------------------------------------------

-- Usage environments annotated to delta variables:
-- The linear variables and proof irrelevant linear variables that suspended on
-- a computation bound to the annotated delta var
newtype UsageEnv = UsageEnv [(Var,Mult)]
-- INVARIANT: Two ocurrences of the same variable must have the same mult
  deriving Eq

makeIrrelevant :: UsageEnv -> UsageEnv
makeIrrelevant (UsageEnv ue) = UsageEnv $ L.map (second makeMultIrrelevant) ue

makeMultIrrelevant :: Mult -> Mult
makeMultIrrelevant (Relevant m)   = Irrelevant m
makeMultIrrelevant (Irrelevant m) = Irrelevant m -- TODO: Oops. We should /not/ normalise this; we need nested irrelevantness, witnessed by the soundness proof
makeMultIrrelevant (Tagged t m) = Tagged t (makeMultIrrelevant m)

lookupUE :: Var -> UsageEnv -> Usage
lookupUE v (UsageEnv m) = maybe Zero LCM (lookup v m)

-- | Delete all occurrences of a Variable
deleteUE :: Var -> UsageEnv -> UsageEnv
deleteUE v (UsageEnv m) = UsageEnv (L.deleteBy ((==) `on` fst) (v,undefined) m)

-- supUE :: UsageEnv -> UsageEnv -> UsageEnv
-- supUE = undefined

-- scaleUE :: Usage -> UsageEnv -> UsageEnv
-- scaleUE Zero ue = ue
-- scaleUE (LCM m) ue = m `undefined` ue

emptyUE :: UsageEnv
emptyUE = UsageEnv mempty

--------------------------------------------------------------------------------
----- Outputable Instances -----------------------------------------------------
--------------------------------------------------------------------------------

instance Outputable IdBinding where
  ppr (LambdaBound m) = text "λ=" GHC.Plugins.<> ppr m
  ppr (DeltaBound an) = text "Δ=" GHC.Plugins.<> ppr an

instance Outputable Mult where
  ppr (Relevant m) = text "@" GHC.Utils.Outputable.<> ppr m
  ppr (Irrelevant m) = text "[@" GHC.Utils.Outputable.<> ppr m GHC.Utils.Outputable.<> text "]"
  ppr (Tagged t m) = ppr m GHC.Utils.Outputable.<> text "#" GHC.Utils.Outputable.<> ppr t

instance Outputable Tag where
  ppr (Tag c i) = ppr c GHC.Utils.Outputable.<> text "_" GHC.Utils.Outputable.<> ppr i

deriving newtype instance Outputable UsageEnv

