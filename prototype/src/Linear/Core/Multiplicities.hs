{-# LANGUAGE GHC2021, ViewPatterns, DerivingVia, GeneralizedNewtypeDeriving, OverloadedRecordDot, LambdaCase, MultiWayIf #-}
module Linear.Core.Multiplicities where

import Control.Monad.Except
import Data.Function
import GHC.Core.Map.Type (deBruijnize)
import GHC.Core.Multiplicity (scaledMult)
import GHC.Types.Var
import GHC.Utils.Outputable
import qualified Data.List as L
import qualified GHC.Core.Multiplicity as C
import qualified GHC.Core.Type as C
import qualified GHC.Plugins
import Control.Monad
import Data.Bifunctor

--------------------------------------------------------------------------------
----- Id Binding ---------------------------------------------------------------
--------------------------------------------------------------------------------

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
data AllowIrrelevant = DisallowIrrelevant | AllowIrrelevant deriving Eq

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
-- fragment that was consumed. (Returns [] if the last resource was consumed)
--
-- Irrelevant-ness of the multiplicities (both input and output) must be
-- handled outside of this function, here they are split just like relevant ones
splitAsNeededThenConsume :: MonadError String m
                         => AllowIrrelevant -> [Tag] -> Mult -> m [Mult]
splitAsNeededThenConsume allowsIrrelevant tagstack m
  | DisallowIrrelevant <- allowsIrrelevant
  , isIrrelevant m = throwError "Tried to use an irrelevant result when not allowed"

  | extractTags m == tagstack
  = pure [] -- consume successfully since the mult tags matches exactly the tagstack

splitAsNeededThenConsume allowsIrrelevant (Tag con i:ts) m
  = join <$> traverse (\case
                 m'@(Tagged (Tag _ i') _)
                    -- From the resources we split, this has the index we are
                    -- looking for, so we keep splitting inside
                    | i' == i -> splitAsNeededThenConsume allowsIrrelevant ts m'

                    -- Otherwise, the resource we need isn't down this path, so
                    -- we can stop splitting here
                    | otherwise -> pure [m']
                 _ -> error "impossible, splitResourceAt guarantees returned resource is tagged"
              )
              (splitResourceAt con m)
-- If there is no tag left then this is the resource we are looking for, so we
-- consume it. We know this is the resource we need because we only recurse
-- after splitting on the index we're looking for. If it's the last tag we're
-- done, otherwise we keep splitting.
splitAsNeededThenConsume allowsIrrelevant [] m
  | DisallowIrrelevant <- allowsIrrelevant
  , isIrrelevant m = throwError "Tried to use an irrelevant result when not allowed"
  | otherwise = pure []

-- | Splits a resource according to a constructor's number of linear fields
splitResourceAt :: GHC.Plugins.DataCon -> Mult -> [Mult]
splitResourceAt con mult = map (\i -> Tagged (Tag con i) mult) [1..numberOfLinearFields con]

numberOfLinearFields :: GHC.Plugins.DataCon -> Int
numberOfLinearFields = length . filter (not . GHC.Plugins.isManyTy . scaledMult) . GHC.Plugins.dataConOrigArgTys

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
makeMultIrrelevant (Irrelevant m) = Irrelevant m
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

