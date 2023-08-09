{-# LANGUAGE GHC2021, ViewPatterns, DerivingVia, GeneralizedNewtypeDeriving, OverloadedRecordDot #-}
module Linear.Core.Multiplicities where

import GHC.Utils.Outputable
import qualified GHC.Core.Multiplicity as C
import GHC.Types.Name.Env
import GHC.Types.Var

data Mult = Relevant C.Mult
          | Irrelevant C.Mult

-- Usage environments annotated to delta variables:
-- The linear variables and proof irrelevant linear variables that suspended on
-- a computation bound to the annotated delta var
newtype UsageEnv = UsageEnv (NameEnv Mult)

data Usage = Zero | LCM Mult

--------------------------------------------------------------------------------
----- Usage Environments -------------------------------------------------------
--------------------------------------------------------------------------------

lookupUE :: Var -> UsageEnv -> Usage
lookupUE = undefined

deleteUE :: Var -> UsageEnv -> UsageEnv
deleteUE = undefined

supUE :: UsageEnv -> UsageEnv -> UsageEnv
supUE = undefined

scaleUE :: Usage -> UsageEnv -> UsageEnv
scaleUE Zero ue = ue
scaleUE (LCM m) ue = m `undefined` ue

--------------------------------------------------------------------------------
----- Outputable Instances -----------------------------------------------------
--------------------------------------------------------------------------------

instance Outputable Mult where
  ppr (Relevant m) = text "Relevant" <+> ppr m
  ppr (Irrelevant m) = text "Irrelevant" <+> ppr m

deriving newtype instance Outputable UsageEnv

