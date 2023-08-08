{-# LANGUAGE GHC2021, ViewPatterns, DerivingVia, GeneralizedNewtypeDeriving, OverloadedRecordDot #-}
{-|
In this module we attempt to implement the linear type system defined in the
thesis.
- Please finish it before implementing it, it'll save me some time.

This implementation works directly on top of Core as defined in GHC, instead of
using a different reduced syntax

-}
module Linear.Core
  ( runLinearCore
  ) where

import GHC.Utils.Outputable
import Control.Monad.Reader
import GHC.Core.UsageEnv
import GHC.Driver.Config.Diagnostic
import GHC.Driver.Config.Core.Lint
import GHC.Plugins
import GHC.Utils.Trace
import GHC.Core.Lint
import GHC.Types.Var.Env
import Data.Map as M
import Data.List as L

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
newtype DeltaAnn = DeltaAnn
  { linear :: UsageEnv
  }
  deriving newtype Outputable

data IdBinding = LambdaBound LCMult  -- lambda
               | DeltaBound DeltaAnn -- both let and case binders
instance Outputable IdBinding where
  ppr (LambdaBound m) = text "LambdaBound" <+> ppr m
  ppr (DeltaBound an) = text "DeltaBound" <+> ppr an

data LCMult = Relevant Mult
            | Irrelevant Mult

instance Outputable LCMult where
  ppr (Relevant m) = text "Relevant" <+> ppr m
  ppr (Irrelevant m) = text "Irrelevant" <+> ppr m

data LCVar = LCVar
  { id :: Var
  , binding :: Maybe IdBinding -- we only have Id bindings for Ids (not for TyVars)
  }

instance Outputable LCVar where
  ppr v = ppr v.id <+> ppr v.binding
instance OutputableBndr LCVar where
  pprPrefixOcc v = ppr v
  pprInfixOcc v = text "`" GHC.Plugins.<> ppr v GHC.Plugins.<> text "`"


runLinearCore :: CoreProgram -> CoreM [SDoc]
runLinearCore pgr = do
  dflags <- getDynFlags 
  let
    localTopBindings = bindersOfBinds pgr
    defcfg = initLintConfig dflags localTopBindings
      
  case initLRes defcfg (inferDeltaAnns pgr) of
                      (w, Nothing) -> pprPanic "inferDeltaAnns failed" (ppr w $$ ppr pgr)
                      (_, Just x) -> pprPanic "ok" (ppr x)
-- TODO : Then pipe inferred output to typechecker action

inferDeltaAnns :: CoreProgram -> LintM LCProgram
inferDeltaAnns = traverse (inferDeltaAnnsBind TopLevel)

inferDeltaAnnsBind :: TopLevelFlag -> CoreBind -> LintM LCBind
inferDeltaAnnsBind topflag (NonRec b e)
  | isId b
  = do (_ty, ue) <- lintCoreExpr e
       e'        <- inferDeltaAnnsExpr e
       return (NonRec (LCVar b (deltaBinding ue)) e')
  | otherwise
  = do e'        <- inferDeltaAnnsExpr e
       return (NonRec (LCVar b Nothing) e')

inferDeltaAnnsBind topflag (Rec (unzip -> (bs,es))) = do
  (unzip -> (_tys, naiveUes)) <- mapM lintCoreExpr es
  pprTraceM "rec things" $ ppr (Rec (zip bs es))
  pprTraceM "naive ues" $ ppr naiveUes
  error "OK"


inferDeltaAnnsExpr :: CoreExpr -> LintM LCExpr
inferDeltaAnnsExpr expr = case expr of
  Var v       -> return (Var v)
  Lit l       -> return (Lit l)
  Type ty     -> return (Type ty)
  Coercion co -> return (Coercion co)
  App e1 e2   -> App <$> inferDeltaAnnsExpr e1 <*> inferDeltaAnnsExpr e2
  Lam b e     -> Lam (LCVar b (multBinding b)) <$> extend LambdaBind b (inferDeltaAnnsExpr e)
  Let bind@(NonRec b _) body
    -> Let <$> inferDeltaAnnsBind NotTopLevel bind
           <*> extend LetBind b (inferDeltaAnnsExpr body)
  Let bind@(Rec bs) body
    -> Let <$> inferDeltaAnnsBind NotTopLevel bind
           <*> extendRecBindings NotTopLevel bs (inferDeltaAnnsExpr body)
  Case e b ty alts -> do
    (_ty, ue) <- lintCoreExpr e
    Case <$> inferDeltaAnnsExpr e
         <*> pure (LCVar b (deltaBinding ue))
         <*> pure ty
         <*> extend CaseBind b (mapM (inferDeltaAnnsAlt ue) alts)

  Tick t e  -> Tick t <$> inferDeltaAnnsExpr e
  Cast e co -> Cast <$> inferDeltaAnnsExpr e <*> pure co

inferDeltaAnnsAlt :: UsageEnv -- ^ The usage environment of the scrutinee
                  -> CoreAlt
                  -> LintM LCAlt
inferDeltaAnnsAlt ue (Alt con args rhs) = do
  rhs' <- extends CasePatBind args $ inferDeltaAnnsExpr rhs
  -- ROMES:TODO: This is wrong for now, we need to update this with the right
  -- way of inferring usage envs. for case pattern variables, but we first
  -- should decide how they typecheck altogether
  let args' = L.map (\a -> LCVar a (deltaBinding ue)) args
  return (Alt con args' rhs')

extend :: BindingSite -> Var -> LintM a -> LintM a
extend s b lact = lintBinder s b $ \_ -> lact

extends :: BindingSite -> [Var] -> LintM a -> LintM a
extends s bs lact = lintBinders s bs $ \_ -> lact

-- extend' :: TopLevelFlag -> BindingSite -> Var -> LintM a -> LintM a
-- extend' t s b lact = lintIdBndr t s b $ \_ -> lact

extendRecBindings :: TopLevelFlag -> [(Var,CoreExpr)] -> LintM a -> LintM a
extendRecBindings flg ids lact = fst <$> lintRecBindings flg ids (\_ -> lact)

-- TODO: The usage environments must be redefined because the multiplicities
-- within may be relevant or irrelevant, and we're currently not accounting that
deltaBinding :: UsageEnv -> Maybe IdBinding
deltaBinding = Just . DeltaBound . DeltaAnn

multBinding :: Var -> Maybe IdBinding
multBinding v
  | isId v    = Just $ LambdaBound $ Relevant (idMult v)
  | otherwise = Nothing

-- computeRecUsageEnvs :: [(Var, UsageEnv)] -- ^ Recursive usage environments associated to their recursive call
--                     -> [(Var, UsageEnv)] -- ^ Non-recursive usage environments
-- computeRecUsageEnvs l =
--   foldl (\acc (v,vEnv) ->
--       map (\(n, nEnv) -> (n, ((fromMaybe 0 $ v `M.lookup` nEnv) `scaleUE` (M.delete v vEnv)) `supUE` (M.delete v nEnv))) acc
--     ) l l
