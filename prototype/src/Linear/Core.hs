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
import Control.Monad.Except
import GHC.Driver.Config.Core.Lint
import GHC.Plugins hiding (Mult)
import GHC.Utils.Trace
import GHC.Types.Var.Env
import Data.Map as M
import Data.List as L
import Data.Maybe
import Data.Functor.Identity

import Linear.Core.Multiplicities
import Linear.Core.Monad

type LCProgram = [LCBind]
type LCBind = Bind LCVar
type LCExpr = Expr LCVar
type LCAlt  = Alt LCVar

{-
I realize now this whole approach of leveraging `lintCoreExpr` to get the usage
environments on a pass before typechecking linear core is likely wrong.
The way Core determines a usage environment is not the same way we do, because
we see linearity and usage of resources in a different way.

Meaning this pass is not fit for our purposes.
 -}

-- | Whenever we recurse into the body of a case expression (whose scrutinee is
-- not in WHNF) to determine the delta annotations of the Delta-bound variables,
-- we need to move the linear variables from the scrutinee to the
-- proof-irrelevant context. This context is needed for 'makeDeltaAnnFrom',
-- which creates a delta-env based on the usage environment of an expression,
-- but requires splitting the resources between proof-irrelevant and relevant.
-- type InferDeltas a = ReaderT (VarEnv LCVar) CoreM

data LCVar = LCVar
  { id :: Var
  , binding :: Maybe IdBinding -- we only have Id bindings for Ids (not for TyVars)
  }


runLinearCore :: CoreProgram -> CoreM [SDoc]
runLinearCore pgr = do
  dflags <- getDynFlags 
  let
    localTopBindings = bindersOfBinds pgr
    defcfg = initLintConfig dflags localTopBindings

    lcprg = runIdentity (convertProgram pgr)

  case runExcept $ runLinearCoreT mempty (checkProgram lcprg) of
    Left e -> return [text e]
    Right x -> pprTraceM "Safe prog:" (ppr x) >> return []

--------------------------------------------------------------------------------
----- Typechecking Linear Core (mostly ignoring types) -------------------------
--------------------------------------------------------------------------------

type LinearCoreM = LinearCoreT (Except String)

checkProgram :: LCProgram -> LinearCoreM LCProgram
checkProgram = traverse checkBind

checkBind :: LCBind -> LinearCoreM LCBind
checkBind (NonRec b e)
  | isId b.id
  = do e' <- record $ checkExpr e
       return (NonRec (LCVar b.id Nothing) e')
  | otherwise
  = do e' <- checkExpr e
       -- This is really instanced to Nothing, since TyVars are not accounted for as linear resources.
       return (NonRec (LCVar b.id Nothing) e')

checkBind (Rec bs) = do
  let (ids,rhss) = unzip bs
  rhss' <- traverse checkExpr rhss
  let ids' = L.map (`LCVar` Nothing) ids
  return (Rec (zip ids' rhss'))

checkExpr :: LCExpr -> LinearCoreM LCExpr
checkExpr expr = case expr of
  Var v       -> return (Var v)
  Lit l       -> return (Lit l)
  Type ty     -> return (Type ty)
  Coercion co -> return (Coercion co)
  App e1 e2   -> App <$> checkExpr e1 <*> checkExpr e2
  Lam b e     -> Lam (LCVar b (multBinding b)) <$> checkExpr e
  Let bind@(NonRec _b _) body
    -> Let <$> checkBind bind
           <*> checkExpr body
  Let bind@(Rec _bs) body
    -> Let <$> checkBind bind
           <*> checkExpr body
  Case e b ty alts -> do
    Case <$> checkExpr e
         <*> pure (LCVar b Nothing)
         <*> pure ty
         <*> mapM (checkAlt ue) alts

  Tick t e  -> Tick t <$> checkExpr e
  Cast e co -> Cast <$> checkExpr e <*> pure co

checkAlt :: UsageEnv -- ^ The scrutinee's usage environment
         -> LCAlt -> LinearCoreM LCAlt
checkAlt ue (Alt con args rhs) = do
  rhs' <- checkExpr rhs
  let args' = L.map (\a -> LCVar a Nothing) args
  return (Alt con args' rhs')


-- | Implements the algorithm to compute the recursive usage environments of a
-- not-necessarily-strongly-connected group of recursive let bindings
computeRecUsageEnvs :: [(Var, UsageEnv)] -- ^ Recursive usage environments associated to their recursive call
                    -> [(Var, UsageEnv)] -- ^ Non-recursive usage environments (vars keep input order)
computeRecUsageEnvs l =
  L.foldl (\acc (v, vEnv) ->
      L.map (\(n, nEnv) -> (n, ((v `lookupUE` nEnv) `scaleUE` (v `deleteUE` vEnv)) `supUE` (v `deleteUE` nEnv))) acc
    ) l l

--------------------------------------------------------------------------------
----- Initial conversion to operate on LCVar binders ---------------------------
--------------------------------------------------------------------------------
-- We make an initial conversion from CoreProgram to LCProgram because our
-- recursive typechecking action operates on LCPrograms.
--
-- This will not populate DeltaBindings correctly, but it will populate correctly LambdaBindings.
-- For DeltaBindings, it'll trivially instantiate the IdBindings to DeltaBound with an empty usage environment.
--
-- The typechecking action will determine the usage environments for each
-- binder during checking, because we already have to calculate the usage environment of the binder bodies.
-- Even if this is not the most optimal strategy, it seems the simplest.

convertProgram :: Monad m => CoreProgram -> m LCProgram
convertProgram = traverse convertBind

convertBind :: Monad m => CoreBind -> m LCBind
convertBind (NonRec b e)
  | isId b
  = do e' <- convertExpr e
       return (NonRec (LCVar b (deltaBinding emptyUE)) e')
  | otherwise
  = do e' <- convertExpr e
       -- This is really instanced to Nothing, since TyVars are not accounted for as linear resources.
       return (NonRec (LCVar b Nothing) e')

convertBind (Rec bs) = do
  let (ids,rhss) = unzip bs
  rhss' <- traverse convertExpr rhss
  let ids' = L.map (`LCVar` (deltaBinding emptyUE)) ids
  return (Rec (zip ids' rhss'))


convertExpr :: Monad m => CoreExpr -> m LCExpr
convertExpr expr = case expr of
  Var v       -> return (Var v)
  Lit l       -> return (Lit l)
  Type ty     -> return (Type ty)
  Coercion co -> return (Coercion co)
  App e1 e2   -> App <$> convertExpr e1 <*> convertExpr e2
  Lam b e     -> Lam (LCVar b (multBinding b)) <$> convertExpr e
  Let bind@(NonRec _b _) body
    -> Let <$> convertBind bind
           <*> convertExpr body
  Let bind@(Rec _bs) body
    -> Let <$> convertBind bind
           <*> convertExpr body
  Case e b ty alts -> do
    Case <$> convertExpr e
         <*> pure (LCVar b (deltaBinding emptyUE))
         <*> pure ty
         <*> mapM (convertAlt) alts

  Tick t e  -> Tick t <$> convertExpr e
  Cast e co -> Cast <$> convertExpr e <*> pure co

convertAlt :: Monad m
           => CoreAlt
           -> m LCAlt
convertAlt (Alt con args rhs) = do
  rhs' <- convertExpr rhs
  let args' = L.map (\a -> LCVar a (deltaBinding emptyUE)) args
  return (Alt con args' rhs')

--------------------------------------------------------------------------------
----- Utilities ----------------------------------------------------------------
--------------------------------------------------------------------------------

deltaBinding :: UsageEnv -> Maybe IdBinding
deltaBinding = Just . DeltaBound

multBinding :: Var -> Maybe IdBinding
multBinding v
  | isId v    = Just $ LambdaBound $ Relevant (idMult v)
  | otherwise = Nothing

--------------------------------------------------------------------------------
----- Outputable Instances -----------------------------------------------------
--------------------------------------------------------------------------------

instance Outputable LCVar where
  ppr (LCVar id' Nothing)  = ppr id'
  ppr (LCVar id' (Just b)) = ppr id' <+> ppr b

instance OutputableBndr LCVar where
  pprPrefixOcc v = ppr v
  pprInfixOcc v = text "`" GHC.Plugins.<> ppr v GHC.Plugins.<> text "`"

--------------------------------------------------------------------------------
----- Attempt 1 - Calling LintM actions for the Usage Env ----------------------
--------------------------------------------------------------------------------

-- Note:
-- Unlike [Attempt 1] in Linear.Core.Plugin, we can't leave this uncommented for typechecking.
-- This code only compiled when using a patched GHC that exposed functions for linting and LintM.
-- We comment it so we can go back to a released GHC version, one with HLS support :)

-- runLinearCore :: CoreProgram -> CoreM [SDoc]
-- runLinearCore pgr = do
--   dflags <- getDynFlags 
--   let
--     localTopBindings = bindersOfBinds pgr
--     defcfg = initLintConfig dflags localTopBindings
      
--   case initLRes defcfg (inferDeltaAnns pgr) of
--                       (w, Nothing) -> pprPanic "inferDeltaAnns failed" (ppr w $$ ppr pgr)
--                       (_, Just x) -> pprPanic "ok" (ppr x)
-- -- TODO : Then pipe inferred output to typechecker action

-- inferDeltaAnns :: CoreProgram -> LintM LCProgram
-- inferDeltaAnns = traverse (inferDeltaAnnsBind TopLevel)

-- inferDeltaAnnsBind :: TopLevelFlag -> CoreBind -> LintM LCBind
-- inferDeltaAnnsBind topflag (NonRec b e)
--   | isId b
--   = do (_ty, ue) <- lintCoreExpr e
--        e'        <- inferDeltaAnnsExpr e
--        return (NonRec (LCVar b (deltaBinding ue)) e')
--   | otherwise
--   = do e'        <- inferDeltaAnnsExpr e
--        return (NonRec (LCVar b Nothing) e')

-- inferDeltaAnnsBind topflag (Rec bs) = do
--   let (ids,rhss) = unzip bs
--   (rhss', naiveUes) <- lintRecBindings topflag bs (\_ -> traverse inferDeltaAnnsExpr rhss)
--   let ids' = L.map (\(id',ue') -> LCVar id' (deltaBinding ue'))
--               $ computeRecUsageEnvs (zip ids naiveUes)
--   return (Rec (zip ids' rhss'))


-- inferDeltaAnnsExpr :: CoreExpr -> LintM LCExpr
-- inferDeltaAnnsExpr expr = case expr of
--   Var v       -> return (Var v)
--   Lit l       -> return (Lit l)
--   Type ty     -> return (Type ty)
--   Coercion co -> return (Coercion co)
--   App e1 e2   -> App <$> inferDeltaAnnsExpr e1 <*> inferDeltaAnnsExpr e2
--   Lam b e     -> Lam (LCVar b (multBinding b)) <$> extend LambdaBind b (inferDeltaAnnsExpr e)
--   Let bind@(NonRec b _) body
--     -> Let <$> inferDeltaAnnsBind NotTopLevel bind
--            <*> extend LetBind b (inferDeltaAnnsExpr body)
--   Let bind@(Rec bs) body
--     -> Let <$> inferDeltaAnnsBind NotTopLevel bind
--            <*> extendRecBindings NotTopLevel bs (inferDeltaAnnsExpr body)
--   Case e b ty alts -> do
--     (_ty, ue) <- lintCoreExpr e
--     Case <$> inferDeltaAnnsExpr e
--          <*> pure (LCVar b (deltaBinding ue))
--          <*> pure ty
--          <*> extend CaseBind b (mapM (inferDeltaAnnsAlt ue) alts)

--   Tick t e  -> Tick t <$> inferDeltaAnnsExpr e
--   Cast e co -> Cast <$> inferDeltaAnnsExpr e <*> pure co

-- inferDeltaAnnsAlt :: UsageEnv -- ^ The usage environment of the scrutinee
--                   -> CoreAlt
--                   -> LintM LCAlt
-- inferDeltaAnnsAlt ue (Alt con args rhs) = do
--   rhs' <- extends CasePatBind args $ inferDeltaAnnsExpr rhs
--   -- ROMES:TODO: This is wrong for now, we need to update this with the right
--   -- way of inferring usage envs for case pattern variables, but we first
--   -- should decide how they typecheck altogether
--   let args' = L.map (\a -> LCVar a (deltaBinding ue)) args
--   return (Alt con args' rhs')

-- extend :: BindingSite -> Var -> LintM a -> LintM a
-- extend s b lact = lintBinder s b $ \_ -> lact

-- extends :: BindingSite -> [Var] -> LintM a -> LintM a
-- extends s bs lact = lintBinders s bs $ \_ -> lact

-- extendRecBindings :: TopLevelFlag -> [(Var,CoreExpr)] -> LintM a -> LintM a
-- extendRecBindings flg ids lact = fst <$> lintRecBindings flg ids (\_ -> lact)

