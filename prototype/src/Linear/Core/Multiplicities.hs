{-# LANGUAGE GHC2021, ViewPatterns, DerivingVia, GeneralizedNewtypeDeriving, OverloadedRecordDot, LambdaCase, MultiWayIf #-}
module Linear.Core.Multiplicities where

import Data.Function
import GHC.Utils.Outputable
import qualified GHC.Core.Multiplicity as C
import GHC.Types.Var
import qualified GHC.Core.Type as C
import GHC.Core.Map.Type (deBruijnize)
import qualified Data.List as L
import qualified GHC.Plugins
import Control.Exception (assert)
import GHC.Core.Multiplicity (scaledMult)

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
isUnrestricted (Tagged _ m) = isUnrestricted m

data Usage = Zero | LCM Mult

-- | Extract all tags of a multiplicity, left to right
--
-- > extractTags 1#(,)_1#Pair_1#K_1 = [(,)_1, Pair_1, K_1]
extractTags :: Mult -> [Tag]
extractTags = reverse . go where go (Tagged t m) = t:go m
                                 go _ = []

-- | Split a resource as needed given a tagstack then consume the resource
-- specified by the tag.
--
-- Returns the resource fragments that were split as needed, except for the
-- fragment that was consumed
splitAsNeededThenConsume :: [Tag] -> Mult -> [Mult]
splitAsNeededThenConsume (Tag con i:ts) m
  = concatMap (\case
                 m'@(Tagged (Tag _ i') _)
                    -- From the resources we split, this has the index we are
                    -- looking for, so we keep splitting inside
                    | i' == i -> splitAsNeededThenConsume ts m'

                    -- Otherwise, the resource we need isn't down this path, so
                    -- we can stop splitting here
                    | otherwise -> [m']
                 _ -> error "impossible, splitResourceAt only returns tagged resources")
              (splitResourceAt con m)
-- If there is no tag left then this is the resource we are looking for, so we
-- consume it. We know this is the resource we need because we only recurse
-- after splitting on the index we're looking for. If it's the last tag we're
-- done, otherwise we keep splitting.
splitAsNeededThenConsume [] _m = []

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
makeIrrelevant (UsageEnv ue) = UsageEnv $ L.map (\(x,m) -> (x,go m)) ue
  where
    go (Relevant m)   = Irrelevant m
    go (Irrelevant m) = Irrelevant m
    go (Tagged t m) = Tagged t (go m)

lookupUE :: Var -> UsageEnv -> Usage
lookupUE v (UsageEnv m) = case lookup v m of
                            Nothing   -> Zero
                            Just mult -> LCM mult

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
  ppr (Relevant m) = text "Relevant" <+> ppr m
  ppr (Irrelevant m) = text "Irrelevant" <+> ppr m
  ppr (Tagged t m) = ppr m GHC.Utils.Outputable.<> text "#" GHC.Utils.Outputable.<> ppr t

instance Outputable Tag where
  ppr (Tag c i) = ppr c GHC.Utils.Outputable.<> text "_" GHC.Utils.Outputable.<> ppr i

deriving newtype instance Outputable UsageEnv

