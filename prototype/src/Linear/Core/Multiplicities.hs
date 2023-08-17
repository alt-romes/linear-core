{-# LANGUAGE GHC2021, ViewPatterns, DerivingVia, GeneralizedNewtypeDeriving, OverloadedRecordDot, LambdaCase #-}
module Linear.Core.Multiplicities where

import Data.Function
import GHC.Utils.Outputable
import qualified GHC.Core.Multiplicity as C
import GHC.Types.Var
import qualified GHC.Core.Type as C
import GHC.Core.Map.Type (deBruijnize)
import qualified Data.List as L
import qualified GHC.Plugins

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

