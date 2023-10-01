{-# LANGUAGE GHC2021, ViewPatterns, DerivingVia, GeneralizedNewtypeDeriving, OverloadedRecordDot #-}
{-|
In this module we attempt to implement the linear type system defined in the
thesis.
- Please finish it before implementing it, it'll save me some time.

This implementation works directly on top of Core as defined in GHC, instead of
using a different reduced syntax

-}
module Linear.Core
  -- ( runLinearCore
  -- )
  where

-- import GHC.Driver.Config.Core.Lint
import Control.Monad.State
import Control.Monad.Except
import Data.List as L
import Data.List.NonEmpty (NonEmpty(..))
import Data.Map.Internal as M
import Data.Maybe
import GHC.Core.TyCo.Rep (Type(..))
import GHC.Plugins hiding (Mult, count, unrestricted)
import GHC.Utils.Outputable as Ppr
import GHC.Utils.Trace

import Linear.Core.Multiplicities
import Linear.Core.Monad
import GHC.Core.Multiplicity (scaledMult)
import Data.Bifunctor

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


-- | Returns an empty list if the program typechecks, and the list of captured
-- errors otherwise
runLinearCore :: CoreProgram -> CoreM [SDoc]
runLinearCore pgr = do
  _dflags <- getDynFlags 
  let
    localTopBindings = bindersOfBinds pgr
    -- The local top-level bindings have empty usage environments, and GlobalIds are treated as constants so we don't need to include them here
    -- See also Note [GlobalId/LocalId]
    bindingsMap = M.fromList $ L.map (,DeltaBound emptyUE) localTopBindings
    -- defcfg = initLintConfig dflags localTopBindings

    lcprg = runIdentity (convertProgram pgr)

  case runIdentity $ runLinearCoreT bindingsMap (checkProgram lcprg) of
    Left e -> do
      -- pprTraceM "Failed to typecheck linearity!" (ppr pgr)
      return [text e]
    Right x -> do
      -- pprTraceM "Safe prog!" (ppr x)
      return []

--------------------------------------------------------------------------------
-- {{{ Typechecking Linear Core (mostly ignoring types) ------------------------
--------------------------------------------------------------------------------

type LinearCoreM = LinearCoreT Identity

checkProgram :: LCProgram -> LinearCoreM LCProgram
checkProgram prog = do
  -- pprTraceM "checkProgram" (ppr prog)
  traverse checkBind prog

-- ROMES:TODO: use isGlobalId and setTopLevelBindingName to set the binding
-- name, s.t. functions started with "fail" don't crash the plugin
checkBind :: LCBind -> LinearCoreM LCBind
checkBind (NonRec b e)
  | isId b.id
  = do (e', ue) <- record $ checkExpr e
       return (NonRec (LCVar b.id (deltaBinding ue)) e')
  | otherwise
  = do e' <- checkExpr e
       -- This is really instanced to Nothing, since TyVars are not accounted for as linear resources.
       return (NonRec (LCVar b.id Nothing) e')

checkBind (Rec bs) = do
  let (ids0,rhss) = unzip bs
  -- pprTraceM "extending with" (ppr ids0)
  inScope :: LCState <- get
  -- We extend the rhss typechecking with the recursive bindings as if they
  -- were linear variables. This way, we record if they are used more than once.
  -- Because we do a dryRun, we won't crash if they are.
  -- Then we use the naiveUsageEnv (the ones computed with the recursive
  -- bindings as linear variables) and compute the real usage environment.
  (_rhss', naiveUsages) <- unzip . fst <$> dryRun
    (extends LetRecBinderDry
         (L.map (\(LCVar b (Just _d)) -> (b, LambdaBound (Relevant OneTy))) ids0)
         (traverse (dryRun . checkExpr) rhss))
  pprTraceM "naiveUsages" (ppr naiveUsages)
  let recUsages = computeRecUsageEnvs (zip (L.map (.id) ids0) naiveUsages)
  pprTraceM "recUsages" (ppr recUsages)

      -- Repeated ocurrences of linear variables will be represented as many
      -- times as they occur in the recursive bindings in the usage
      -- environments with a linear multiplicity.
      -- In practice, when recursive binders are used, we'll try to use the linear variables more than once, if they exist more than once
  recUes <- mapM (\i -> extends LetRecBinder (L.map (\id' -> (id'.id, DeltaBound emptyUE)) ids0) $ reconstructUe i.id recUsages inScope) ids0

  let ids1 = L.zipWith (\i b -> LCVar i.id (deltaBinding b)) ids0 recUes
  pprTraceM "Recursive bindings:" (ppr ids1)

  -- Must typecheck rhss' again with the correct recursive usage environments
  rhss' <- extends LetRecBinder (L.map (\(LCVar i (Just b)) -> (i,b)) ids1) (traverse checkExpr rhss)
  return (Rec (zip ids1 rhss'))

checkExpr :: LCExpr -> LinearCoreM LCExpr
checkExpr expr = case expr of
  Var v       -> use v >> return (Var v)
  Lit l       -> return (Lit l)
  Type ty     -> return (Type ty)
  Coercion co -> return (Coercion co)
  App e1 e2
    -- romes:todo: could also be mult. app, in which case we should substitute mults in body by arg mult
    | FunTy _ ManyTy _ _ <- exprType (unconvertExpr e1)
    -> App <$> checkExpr e1 <*> unrestricted (checkExpr e2)
    | otherwise -- Linear or variable multiplicity (still linear) arrow
    -> App <$> checkExpr e1 <*> checkExpr e2
  Lam b e 
    -- We use make type variables unrestricted in the environment (fromMaybe)
    -> Lam b <$> extend LambdaBinder b.id (fromMaybe (LambdaBound (Relevant ManyTy)) (multBinding b.id)) (checkExpr e)
  Let bind@(NonRec _b _) body
    | isId _b.id
    -> do
      bind'@(NonRec (LCVar b (Just delta')) _) <- restoringState $ checkBind bind
      Let bind'
          <$> extend LetBinder b delta' (checkExpr body)

    -- We ignore multiplicity semiring and type abstractions, just check linearity
    | otherwise
    -> do
      bind'@(NonRec (LCVar _ Nothing) _) <- restoringState $ checkBind bind
      Let bind' <$> checkExpr body
  Let bind@(Rec _bs) body
    -> do
      bind'@(Rec (unzip -> (bs, _))) <- restoringState $ checkBind bind
      Let bind'
          <$> extends LetRecBinder (L.map (\(LCVar b (Just d)) -> (b,d)) bs) (checkExpr body)
  casee@(Case e b ty alts)
    -- Expression is in WHNF (See Note [exprIsHNF] and #23771, function is really "exprIsWHNF")
    | exprIsHNF (unconvertExpr e)
    -> do
      lcs0 <- get
      (e', ue) <- record $ checkExpr e
      Case e'
           (LCVar b.id (deltaBinding ue))
           ty
       <$> withSameEnvMap (\alt -> do
            put lcs0 -- we restore the state for each alternative, not before (otherwise resources aren't consumed in the EmptyCase)
            extend CaseBinder b.id (DeltaBound ue) $
              checkAlt ue b.id (exprType (unconvertExpr e)) alt) alts
    | otherwise
    -- Expression is definitely not in WHNF (or do we really mean HNF?)
    -> do -- pprTrace "Case expression" (ppr casee) $ do

      -- We restore the resources here because we make them irrelevant in the env. afterwards
      lcs0 <- get
      (e', ue) <- record $ checkExpr e
      let irrUe = makeIrrelevant ue
      pprTraceM "Make irrelevant usage environment:" (ppr irrUe) 
      Case e'
           (LCVar b.id (deltaBinding irrUe))
           ty
       <$> withSameEnvMap (\alt -> do
            put lcs0 -- we restore the state for each alternative, not before (otherwise resources aren't consumed in the EmptyCase)
            makeEnvResourcesIrrelevant ue
            extend CaseBinder b.id (DeltaBound irrUe) $
              checkAlt irrUe b.id (exprType (unconvertExpr e)) alt) alts

  Tick t e  -> Tick t <$> checkExpr e
  Cast e co -> Cast <$> checkExpr e <*> pure co

checkAlt :: UsageEnv -- ^ The scrutinee's usage environment
         -> Var      -- ^ Case binder name
         -> Type     -- ^ Scrutinee type
         -> LCAlt -> LinearCoreM LCAlt

--- * ALT_
checkAlt _ _ _ (Alt DEFAULT [] rhs) = do
  rhs' <- checkExpr rhs
  return (Alt DEFAULT [] rhs')

checkAlt _ _ _ (Alt DEFAULT _ _) = error "impossible"

--- * ALT0
checkAlt ue zbind _ (Alt (LitAlt l) [] rhs) = do
  rhs' <- Linear.Core.Monad.drop ue >> dropEnvOf zbind >> checkExpr rhs
  return (Alt (LitAlt l) [] rhs')

checkAlt _ _ _ (Alt (LitAlt _) _ _) = error "impossible"

--- * ALT0
checkAlt ue zbind s_ty a@(Alt (DataAlt con) args rhs)
  | all (isManyTy . scaledMult) (uniDataConOrigArgTys con s_ty)
  = pprTrace "ALT0 con" (ppr a Ppr.<> Ppr.text ". (UE):" Ppr.<> ppr ue) $ do
          -- Add unrestricted and coercion binders
  rhs' <- extends PatternBinder (L.map (\arg -> (arg.id, LambdaBound (Relevant ManyTy))) args)
          -- Drop from the environment the fully used resources
          $ Linear.Core.Monad.drop ue
          -- Drop from the binder environment the fully used resources to make it unrestricted
          >> dropEnvOf zbind
          >> checkExpr rhs
  return (Alt (DataAlt con) args rhs')

--- * ALTN
-- We do the simplest thing here:
--  Split the environment by all pattern variables, regardless of the scrutinee expression
-- We need to correctly assign exactly the resources from the scrutinee to each pattern variable in theory, because the substitution lemma can't be applied to case pattern vars otherwise.
-- But in practice, it's sufficient to assign split (tagged) resources to all pattern variables -- it is enough to ensure they are all used exclusively.
-- We do lose the ability to make a linear pattern variable unrestricted if no resources were assigned to it, but that's probably never going to happen in the transformations.
-- It's probably not worth it trying to be that smart, and we don't do substitution here (only checking). Even if we did substituttion things would likely work since all linear variables are used once, despite the theory not working
-- TODO: Do the simple thing
checkAlt ue _z s_ty alt@(Alt (DataAlt con) args rhs) = pprTrace "ALTN con" (ppr alt) $ do

  -- pprTraceM "Constructor type" (ppr (dataConRepType con))
  -- pprTraceM "Constructor arguments:" (ppr args <+> ppr (dataConUnivTyVars con) <+> ppr (dataConExTyCoVars con) <+> ppr (dataConUnivAndExTyCoVars con) <+> ppr (dataConTheta con) <+> ppr (zip3 (dataConOrigArgTys con) (scaledMult <$> dataConOrigArgTys con) (uniDataConOrigArgTys con s_ty)) <+> ppr (dataConRepArgTys con))

  let (unrestricted_args, linear_args) = bimap (L.map snd) (L.map snd) $
                                          L.partition (isManyTy . fst)
                                                      (zip (L.map scaledMult (uniDataConOrigArgTys con s_ty)) (L.drop nonOrigArgsLength args)
                                                      ++ L.map (ManyTy,) (L.take nonOrigArgsLength args)) -- then re-add the things we dropped as unrestricted things
                                                        where
                                                          -- We need to drop all things which we don't care about for in linearity.
                                                          -- see DataCon (eg type variables, coercions, constraints)
                                                          nonOrigArgsLength = length (dataConExTyCoVars con) + dataConRepArity con - dataConSourceArity con

--   pprTraceM "Unr args in ALTN con:" (ppr unrestricted_args)

  -- Add the tag the usage environment with the linear resources with this constructor and an index for each
  -- It will ensure that when we consume the resources by using this environment, we'll just split the resource according to the tag.
  let linear_args' = L.zipWith (\a i -> (a.id, deltaBindingTagged con i ue)) linear_args [1..]
  -- pprTraceM "Linear args in ALTN con:" (ppr linear_args')

          -- First, extend computation with unrestricted resources
  rhs' <- extends PatternBinder (L.map ((, LambdaBound (Relevant ManyTy)) . (.id)) unrestricted_args)
          -- Then, with linear resources
          $ extends PatternBinder linear_args'
          $ checkExpr rhs

  return (Alt (DataAlt con) (unrestricted_args ++ L.map (uncurry LCVar . second Just) linear_args') rhs')

-- }}}
--------------------------------------------------------------------------------
-- {{{ Algorithms for computing usage environments -----------------------------
--------------------------------------------------------------------------------

-- | Reconstruct the usage environment for a given variable with
--  1. The counts of usages in a group of recursive bindings
--  2. The In Scope Variables and their corresponding bindings
reconstructUe :: forall m. (MonadFail m, MonadError String m) => Var -> [(Var, M.Map Var Int)] -> LCState -> m UsageEnv
reconstructUe v usageMap inscope = do
  Just usages <- pure $ L.lookup v usageMap
  M.foldlWithKey go (return $ UsageEnv []) usages
  where
    go :: m UsageEnv -> Var -> Int -> m UsageEnv
    go mue var count = do
      UsageEnv acc  <- mue
      case M.lookup var inscope of
        Nothing ->
          -- We might not find the variable in the inscope set if the variable is
          -- bound by the recursive binder (the rec binder is a rec function)
          if isId var && not (isManyTy (varMult var)) && count /= 1
             then
              throwError $ "Used a linear variable bound in a recursive let binding group not linearly: " ++ showPprUnsafe var ++ " ; " ++ showPprUnsafe (usageMap, inscope)
             else
              -- If all is well, we continue with the usage env acc, but don't
              -- add this var to the u.e. of the recursive binder, as it is not a
              -- free linear variable in the binder
              return (UsageEnv acc)
        Just binding -> return $ UsageEnv $ go' var count binding ++ acc

    go' :: Var -> Int -> Either IdBinding (NonEmpty Mult) -> [(Var, Mult)]
    go' var count (Left (LambdaBound mult)         ) = replicate count (var,mult)
    go' _   count (Left (DeltaBound (UsageEnv env))) = concat $ replicate count env
    go' var count (Right mults) -- kind of dreadful, but we don't delete the last tagged multiplicity, simply record it; if otherwise this isn't the last, then it wasn't fully consumed ? In that case, how did we get hold of the var? maybe it's impossible
      | mult:|[] <- mults = replicate count (var, removeTag mult)
      | otherwise = error "How did we get hold of this variable?"

-- | Implements the algorithm to compute the recursive usage environments of a
-- not-necessarily-strongly-connected group of recursive let bindings
-- computeRecUsageEnvs :: [(Var, UsageEnv)] -- ^ Recursive usage environments associated to their recursive call
--                     -> [(Var, UsageEnv)] -- ^ Non-recursive usage environments (vars keep input order)
-- computeRecUsageEnvs l =
--   L.foldl (\acc (v, vEnv) ->
--       L.map (\(n, nEnv) -> (n, ((v `lookupUE` nEnv) `scaleUE` (v `deleteUE` vEnv)) `supUE` (v `deleteUE` nEnv))) acc
--     ) l l

-- | Instead of the above, we compute the recursive usage environments from all
-- variable occurrences, not just the usage environments.
computeRecUsageEnvs :: [(Var, M.Map Var Int)] -- ^ Recursive usage environments associated to their recursive call
                    -> [(Var, M.Map Var Int)] -- ^ Non-recursive usage environments
computeRecUsageEnvs l =
  L.foldl (flip $ \(v,vEnv) -> L.map $ \(n, nEnv) ->
      (n, (fromMaybe 0 (v `M.lookup` nEnv) `scale` M.delete v vEnv) `sup` M.delete v nEnv)) l l
  where
    sup :: M.Map Var Int -> M.Map Var Int -> M.Map Var Int
    sup = M.merge M.preserveMissing M.preserveMissing (M.zipWithMatched $ \_ x y -> max x y)
      
    scale :: Int -> M.Map Var Int -> M.Map Var Int
    scale m = M.map (*m)

-- }}}
--------------------------------------------------------------------------------
-- {{{ Initial conversion to operate on LCVar binders --------------------------
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
  let ids' = L.map (`LCVar` deltaBinding emptyUE) ids
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
         <*> mapM convertAlt alts

  Tick t e  -> Tick t <$> convertExpr e
  Cast e co -> Cast <$> convertExpr e <*> pure co

convertAlt :: Monad m
           => CoreAlt
           -> m LCAlt
convertAlt (Alt con args rhs) = do
  rhs' <- convertExpr rhs
  let args' = L.map (\a -> LCVar a (deltaBinding emptyUE)) args
  return (Alt con args' rhs')

-- }}}
--------------------------------------------------------------------------------
-- {{{ Utilities ---------------------------------------------------------------
--------------------------------------------------------------------------------

-- | Alias for @Just . DeltaBound@
deltaBinding :: UsageEnv -> Maybe IdBinding
deltaBinding = Just . DeltaBound

deltaBindingTagged :: DataCon -> Int -- index
                   -> UsageEnv -> IdBinding
deltaBindingTagged con i (UsageEnv vs) = DeltaBound $ UsageEnv $ L.map (second (Tagged (Tag con i))) vs

multBinding :: Var -> Maybe IdBinding
multBinding v
  | isId v    = Just $ LambdaBound $ Relevant (idMult v)
  | otherwise = Nothing

-- }}}
--------------------------------------------------------------------------------
-- {{{ Initial conversion to operate on LCVar binders --------------------------
--------------------------------------------------------------------------------
-- This is the product of realizing later on that we need the original
-- expressions to use Core functions, e.g. to call exprIsWHNF
-- We might have been able to get away with deriving functor for Expr, and then mapping over it, but oh well.

unconvertBind :: LCBind -> CoreBind
unconvertBind (NonRec b e) = NonRec b.id (unconvertExpr e)
unconvertBind (Rec bs) =
  let (ids,rhss) = unzip bs
      rhss' = L.map unconvertExpr rhss
      ids' = L.map (.id) ids
   in Rec (zip ids' rhss')


unconvertExpr :: LCExpr -> CoreExpr
unconvertExpr expr = case expr of
  Var v       -> Var v
  Lit l       -> Lit l
  Type ty     -> Type ty
  Coercion co -> Coercion co
  App e1 e2   -> App (unconvertExpr e1) (unconvertExpr e2)
  Lam b e     -> Lam b.id (unconvertExpr e)
  Let bind body
    -> Let (unconvertBind bind)
           (unconvertExpr body)
  Case e b ty alts -> do
    Case (unconvertExpr e)
         b.id
         ty
         (L.map unconvertAlt alts)

  Tick t e  -> Tick t (unconvertExpr e)
  Cast e co -> Cast (unconvertExpr e) co

unconvertAlt :: LCAlt -> CoreAlt
unconvertAlt (Alt con args rhs) =
  let rhs' = unconvertExpr rhs
      args' = L.map (.id) args
   in Alt con args' rhs'

-- }}}
--------------------------------------------------------------------------------
-- {{{ Outputable Instances ----------------------------------------------------
--------------------------------------------------------------------------------

instance Outputable LCVar where
  ppr (LCVar id' Nothing)  = ppr id'
  ppr (LCVar id' (Just b)) = ppr id' <+> ppr b

instance OutputableBndr LCVar where
  pprPrefixOcc = ppr
  pprInfixOcc v = text "`" GHC.Plugins.<> ppr v GHC.Plugins.<> text "`"

-- }}}
--------------------------------------------------------------------------------
-- {{{ Attempt 1 - Calling LintM actions for the Usage Env ---------------------
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

-- }}}
--------------------------------------------------------------------------------
-- foldenable
-- vim: fdm=marker
