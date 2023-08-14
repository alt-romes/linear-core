{-# LANGUAGE GHC2021, ViewPatterns, DerivingVia, GeneralizedNewtypeDeriving, OverloadedRecordDot #-}
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
isBindingLinear _ = False

--------------------------------------------------------------------------------
----- Multiplicities -----------------------------------------------------------
--------------------------------------------------------------------------------

data Mult = Relevant C.Mult
          | Irrelevant C.Mult

-- ROMES:TODO: This is an incorrect instance of equality for mults because of mult. vars.
instance Eq Mult where
  Relevant m1 == Relevant m2 = deBruijnize m1 == deBruijnize m2
  Irrelevant m1 == Irrelevant m2 = deBruijnize m1 == deBruijnize m2
  _ == _ = False

isLinear :: Mult -> Bool
isLinear = not . isUnrestricted

isUnrestricted :: Mult -> Bool
isUnrestricted (Relevant m)   = C.isManyTy m
isUnrestricted (Irrelevant m) = C.isManyTy m

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
makeIrrelevant (UsageEnv ue) = UsageEnv $ M.map (\case Relevant m -> Irrelevant m; Irrelevant m -> Irrelevant m) ue

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

deriving newtype instance Outputable UsageEnv

