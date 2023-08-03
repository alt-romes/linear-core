{-|
In this module we attempt to implement the linear type system defined in the
thesis.
- Please finish it before implementing it, it'll save me some time.

This implementation works directly on top of Core as defined in GHC, instead of
using a different reduced syntax

-}
module Linear.Core where

import Control.Monad.Reader
import GHC.Core.UsageEnv
import GHC.Plugins
import GHC.Core.Lint
import GHC.Types.Var.Env
import Data.Map as M

type LCProgram = [LCBind]
type LCBind = Bind LCVar
type LCExpr = Expr LCVar
type LCAlt  = Alt LCVar

-- | Whenever we recurse into the body of a case expression (whose scrutinee is
-- not in WHNF) to determine the delta annotations of the Delta-bound variables,
-- we need to move the linear variables from the scrutinee to the
-- proof-irrelevant context. This context is needed for 'makeDeltaAnnFrom',
-- which creates a delta-env based on the usage environment of an expression,
-- but requires splitting the resources between proof-irrelevant and relevant.
type InferDeltas a = ReaderT (VarEnv LCVar) CoreM

-- Usage environments annotated to delta variables:
-- The linear variables and proof irrelevant linear variables that suspended on
-- a computation bound to the annotated delta var
data DeltaAnn = DeltaAnn
  { linear :: UsageEnv
  , proof_irrelevant :: UsageEnv
  }

data IdBinding = LambdaBound Mult    -- lambda
               | DeltaBound DeltaAnn -- both let and case binders

data LCVar = LCVar
  { id :: Var
  , binding :: Maybe IdBinding -- we only have Id bindings for Ids (not for TyVars)
  }


runLinearCore :: CoreProgram -> CoreM [SDoc]
runLinearCore = undefined

inferDeltaAnns :: CoreProgram -> LintM LCProgram
inferDeltaAnns = traverse inferDeltaAnnsBind

inferDeltaAnnsBind :: CoreBind -> LintM LCBind
inferDeltaAnnsBind (NonRec b e) = do
  (ty, ue) <- lintCoreExpr e
  deltaAnn <- makeDeltaAnnFrom ue
  _

inferDeltaAnnsExpr :: CoreExpr -> LintM LCExpr
inferDeltaAnnsExpr expr = do


makeDeltaAnnFrom :: UsageEnv -> DeltaAnn
makeDeltaAnnFrom ue = _
