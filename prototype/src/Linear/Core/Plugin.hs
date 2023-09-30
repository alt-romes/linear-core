{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Linear.Core.Plugin where

{-
Implementation Notes:

fromCore and fromBind will take a Core expression and convert it into a LinearCore expression.
This conversion isn't complete: the usage environments are only inferred in a
subsequent pass 'inferUsageEnvironments'.
Only after the usage environments are inferred can the expressions be typechecked.

* (We could likely compute the usage environment of non-rec lets while converting the expressions, but for let recs it's harder)

* This module is looking way too confusing:
Perhaps re-do the implementation directly on Core instead of Linear.Core.

--------
Using usage environments instead of unrestricted and linear resources (empty UE vs exactly one UE vs complex UE):
* this isn't useful for linear resources, since they would be duplicated
 -}

import Data.Functor hiding (unzip)
import Data.Void
import Data.Text (Text)
import qualified Data.Text as T
-- import Prettyprinter

import qualified GHC.Utils.Outputable as Ppr
import GHC.Core.TyCon
import GHC.Core.TyCo.Rep
import GHC.Types.Var
import GHC.Plugins
import Control.Monad
import Control.Monad.Reader
import Control.Monad.Except
import qualified GHC.Utils.Trace as Trace

-- import qualified Linear.Core.Translate.Syntax as LC
-- import qualified Linear.Core.Translate.Check as LC
import GHC.Core.Map.Type
import Data.Maybe

import Linear.Core
import qualified Data.List as L

-- type CoreCheck = ReaderT CoreProgram (ExceptT (Doc Void) CoreM)
-- type CoreConv  = ReaderT (VarEnv LC.Var) CoreCheck

plugin :: Plugin
plugin = defaultPlugin { installCoreToDos = install }

install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install _opts todo =
  return (concatMap (:[CoreDoPluginPass "Linear Core Pass" linearCorePass]) todo)

--------------------------------------------------------------------------------
----- Attempt 2 - Typecheck Linearity in Core directly--------------------------
--------------------------------------------------------------------------------

linearCorePass :: ModGuts -> CoreM ModGuts
linearCorePass guts = do
  let prog = mg_binds guts

  msgs <- Linear.Core.runLinearCore prog
  case msgs of
    [] -> do
      Trace.pprTraceM "[SUCCESS]" (ppr ())
    errs ->
      -- if all (L.isPrefixOf "fail_" . showSDocUnsafe) errs
       -- the fail_ thing was an attempt to allow the plugin to continue on
       -- functions marked for failing, but that feature isn't finished
       -- then fatalErrorMsg (ppr errs)
       Trace.pprTraceM "[FAILED]" (ppr errs Ppr.$$ ppr prog)

  -- We use a simple bash script to count SUCCESS and FAILED
  return guts -- unchanged guts, after validating them.

--------------------------------------------------------------------------------
----- Attempt 1 - From Core to Linear Core first -------------------------------
----- See also Linear.Core.Translate.* modules ---------------------------------
--------------------------------------------------------------------------------
-- Everything below this line is unused, but still typechecks

--validateLinearGuts :: ModGuts -> CoreM ModGuts
--validateLinearGuts guts = do
--  let prog = mg_binds guts

--  msgs <- runExceptT (runReaderT (forM_ prog validateBind) prog)
--  case msgs of
--    Right () -> pure ()
--    Left e -> fatalErrorMsgS (show e)

--  return guts -- unchanged guts, after validating them.

---- LC.Binder and the type of the bound expression
----
---- Perhaps we should guarantee the bindings are already strongly connected
--validateBind :: CoreBind -> CoreCheck () 
--validateBind b = do
--  printP b
--  lcBind <- runConv (fromBind b)
--  printPretty "Validate Bind" lcBind
--  lift . liftEither $
--    case lcBind of
--      LC.NonRec _ e -> void $ LC.runCheck mempty (LC.typecheck e)
--      LC.Rec (unzip -> (bs,es)) -> void $ LC.runCheck mempty (LC.extends bs $ traverse LC.typecheck es)


--validateExpr :: CoreExpr -> CoreCheck (LC.CoreExpr, LC.Ty)
--validateExpr e = do
--  printP e
--  Just lcExpr <- runConv (fromCore e)
--  printPretty "Validate Expression" lcExpr
--  lift . liftEither $
--    LC.runCheck mempty (LC.typecheck lcExpr)

---- LC.Binder and the type of the bound expression
----
---- Perhaps we should guarantee the bindings are already strongly connected
--fromBind :: CoreBind -> CoreConv LC.CoreBind 
--fromBind (NonRec b e)
--  | Just b' <- fromLamVar b <&> (`LC.setIdBinding` LC.DeltaBound mempty)
--  = do
--    Just e' <- fromCore e
--    return (LC.NonRec b' e')
--  | otherwise
--  = error "validateBind: type lets not supported"
--fromBind (Rec (unzip -> (bs,es)))
--  | Just bs' <- traverse fromLamVar bs <&> map (`LC.setIdBinding` LC.DeltaBound mempty)
--  = do
--    Just es' <- sequenceA <$> extends (zip bs bs') (mapM fromCore es)
--    return (LC.Rec (zip bs' es'))
--  | otherwise
--  = error "validateBind: type lets not supported"

---- | From Core returns a Maybe expression because Linear Core doesn't represent
---- the entirety of Core.
----
---- In particular, it doesn't have Coercions nor Type abstractions and
---- applications (only Multiplicity abstractions)
----
---- For other cases it should return Just
--fromCore :: CoreExpr -> CoreConv (Maybe LC.CoreExpr)
--fromCore = \case
--  Var var -> do
--    env <- ask
--    -- If the variable doesn't exist we make it an unrestricted free variable,
--    -- it likely is imported -- and so has an empty environment (since it's a top-level (closed) let bound definiton).
--    let var' = lookupWithDefaultVarEnv env (LC.Id (fromType $ varType var) (LC.DeltaBound mempty) (varNameT var)) var
--    return $ Just $ LC.Var var'
--  Lit lit -> return $ Just $ LC.Lit (LC.L lit)
--  App e1 e2 -> do
--    e1' <- fromJust <$> fromCore e1 -- should always succeed, we don't apply types and coercions to anything in a well typed expression
--    e2' <- fromCore e2
--    case e2' of
--      Just e2'' -> return $ Just $ LC.App e1' e2''
--      Nothing ->
--        -- We used to apply this to an expression we aren't able to represent
--        -- in linear core, which must have been a type or a coercion, so, if Core was well typed,
--        -- then e1' must have been a type lambda which we deleted, so just return e1'
--        return $ Just e1'
--  Lam b e
--    | Just b' <- fromLamVar b
--    -> do
--      Just e' <- extend b b' (fromCore e) -- the body of the lambda can't just be a type in a well-typed expression, can it?
--      return $ Just $ LC.Lam b' e'
--    | otherwise
--    -- type abstractions are removed
--    -> fromCore e

--  Let (NonRec b e1) e2
--    | Just b' <- fromDeltaVar b
--    -> do
--      Just e1' <- fromCore e2
--      Just e2' <- extend b b' (fromCore e1)
--      return $ Just $ LC.Let (LC.NonRec b' e1') e2'
--    | otherwise -> error "hwat"

--  Let (Rec (unzip . filter (isId . fst) -> (bs,es))) e'
--    | Just bs' <- traverse fromDeltaVar bs
--    -> do
--      Just es' <- sequence <$> traverse (extends (zip bs bs') . fromCore) es
--      Just e'' <- extends (zip bs bs') $ fromCore e'
--      return $ Just $ LC.Let (LC.Rec (zip bs' es')) e''
--    | otherwise -> error "hwat"

--  Case e b _t alts
--    | Just b' <- fromDeltaVar b
--    -> do
--      Just e' <- fromCore e
--      alts' <- traverse (extend b b' . fromCoreAlt) alts
--      return $ Just $ LC.Case e' b' alts'

--    | otherwise -> error "what"

--  Cast e _co -> fromCore e -- ignore coercions
--  Tick _tick e -> fromCore e -- and ticks

--  Type t -> return $ do
--    m <- fromTypeMult t -- if this fails, this type is not a mult type, so we delete it by returning Nothing
--    pure $ LC.Mult m

--  Coercion _co -> error "Coercion" -- how to handle moving from coercion to expr? where can coercions occur?

--fromCoreAlt :: CoreAlt -> CoreConv LC.CoreAlt
--fromCoreAlt (Alt con bs e)
--  | Just bs' <- traverse fromLamVar bs
--  = do
--    let con' = fromCoreAltCon con
--    Just e' <- extends (zip bs bs') (fromCore e)
--    return $ LC.Alt con' bs' e'

--  | otherwise = error "what"

--fromCoreAltCon :: AltCon -> LC.AltCon LC.Var
--fromCoreAltCon = \case
--  DEFAULT  -> LC.DEFAULT
--  LitAlt l -> LC.DataAlt (LC.DataCon (literalNameT l) [] [])
--  DataAlt dc -> LC.DataAlt (LC.DataCon (dataConNameT dc) (map fromMultVar $ filter hasVarKindMult $ dataConUnivTyVars dc) (map (fromCoreScaled fromType) $ dataConOrigArgTys dc))

--fromCoreScaled :: (a -> b) -> Scaled a -> LC.Scaled b
--fromCoreScaled from (Scaled m a) = LC.Scaled (fromMult m) (from a)

---- In 'fromVar' this also needs to take a binding site (does it reallly matter ? perhaps
---- we could always talk about usage environments, which might be empty
---- (unrestricted), have exactly the same variable (linear), or otherwise) and
---- the usage environment
---- TODO ^^^^!
----
---- (Instead, we make it fromLamVar and mkLetVar?

--fromLamVar :: Var -> Maybe LC.Var
--fromLamVar b
--  | hasVarKindMult b
--  = Just $ LC.MultVar $ varNameT b

--  -- ignore multiplicity expressions for abstractions other than multiplicity ones
--  | isTyVar b
--  = Nothing

--  | isId b
--  -- perhaps we can implicitly treat all ocurrences of polymorphic variables as
--  -- atomic types
--  = Just $ LC.Id (fromType $ varType b) (LC.LambdaBound (fromMult (varMult b))) (varNameT b)
--  | otherwise = error "impossible"

--fromDeltaVar :: Var -> Maybe LC.Var
--fromDeltaVar b
--  | hasVarKindMult b
--  = Just $ LC.MultVar $ varNameT b

--  -- ignore multiplicity expressions for abstractions other than multiplicity ones
--  | isTyVar b
--  = Nothing

--  | isId b
--  -- We always use an empty delta environment when translating.
--  -- In the subsequent "inference" pass we can determine the correct usage environments.
--  = Just $ LC.Id (fromType $ varType b) (LC.DeltaBound mempty) (varNameT b)
--  | otherwise = error "impossible"

---- | INVARIANT: Var has kind Mult!
--fromMult :: Mult -> LC.Mult
--fromMult m
--  | deBruijnize m == deBruijnize OneTy
--  = LC.One
--  | deBruijnize m == deBruijnize ManyTy
--  = LC.Many
--  -- multiplicity var case, since we know m is a multiplicity
--  | TyVarTy v <- m
--  = LC.MV $ varNameT v
--  | otherwise = error "impossible"

---- INVARIANT: Var has kind kult
--fromMultVar :: Var -> LC.Mult
--fromMultVar v = LC.MV' $ LC.MkMultVar (varNameT v)

---- | Return Just Mult if the Type has kind Mult (is a multiplicity) and Nothing otherwise
--fromTypeMult :: Type -> Maybe LC.Mult
--fromTypeMult ty
--  | deBruijnize (typeKind ty) == deBruijnize multiplicityTy
--  = Just $ fromMult ty
--  | otherwise
--  = Nothing

---- | Since we delete some parts of terms we don't support in linear core,
---- we simplify some types to match the term level decisions
--fromType :: HasCallStack => Type -> LC.Ty
--fromType = \case
--  TyVarTy v -> -- error $ "A type variable " ++ show (varNameT v) ++ " by itself is not a type, since multiplicities only appear in functions?"
--    -- We might be calling fromType e.g. on the type of an imported expression, which might have polymorphic type variables
--    -- Se simply replace all type vars by their name, as if they were atoms, because we don't care about type polymorphism.
--    LC.Datatype (varNameT v) []
--  AppTy t1 t2 -> -- We can treat an AppTy as a data constructor name... with spaces... for type variables :)?
--    error $ "This is for higher kinded var types applications: " ++ showPprUnsafe (ppr $ AppTy t1 t2)

--  -- Look through pattern synonyms
--  TyConApp tc _
--    | Just rhsty <- synTyConRhs_maybe tc
--    -> fromType rhsty 

--  -- what happens if we have data K a b = K a b, where a b are type variables
--  -- (not mult vars)? If we drop a b, we get K a b... Maybe we really need to
--  -- accept that?
--  --
--  -- Or, what if we define the typechecking algorithm on top of Core itself...
--  -- wouldn't that be easier...?
--  --
--  -- Rather, let's just replace all type variables by () xD, so even if we
--  -- delete them from here it will otherwise match.
--  --
--  -- Nope.
--  TyConApp tc kotys -> LC.Datatype (tcNameT tc) (mapMaybe fromTypeMult kotys)
--  ForAllTy (binderVar -> b) ty
--    | hasVarKindMult b
--    -> LC.Scheme (varNameT b) (fromType ty)
--    | otherwise
--    -> fromType ty -- we delete schemes that are not multiplicity schemes
--  FunTy _flg mult t1 t2 -> LC.FunTy (fromType t1) (fromMult mult) (fromType t2)
--  LitTy tylit -> LC.Datatype (pprT tylit) []
--  CastTy ty _co -> fromType ty
--  CoercionTy _co -> error "We should never try to get the type of a coercion?"


---- Tomorrow: maybe try defining the typechecking algorithm on Core directly, instead of converting it.
---- No, it won't work because the current Core doesn't carry the things we need
---- Well, MAYBE, we can have something isomorphic to Expr (Var,Maybe IdBinding)
---- But that's still more complicated than a translation.


--runConv :: CoreConv a -> CoreCheck a
--runConv = flip runReaderT mempty

--varNameT :: Var -> Text
--varNameT = T.pack . showPprUnsafe . varName

--literalNameT :: Literal -> Text
--literalNameT l = T.pack (showPprUnsafe l)

--dataConNameT :: DataCon -> Text
--dataConNameT dc = T.pack (showPprUnsafe $ dataConName dc)

--tcNameT :: TyCon -> Text
--tcNameT = T.pack . showPprUnsafe . tyConName

--extend :: Var -> LC.Var -> CoreConv a -> CoreConv a
--extend b b' = local (\ve -> extendVarEnv ve b b')

--extends :: [(Var, LC.Var)] -> CoreConv a -> CoreConv a
--extends bs = local (`extendVarEnvList` bs)

---- | Is this a type variable with a Multiplicity kind
--hasVarKindMult :: Var -> Bool
--hasVarKindMult v = isTyVar v && deBruijnize (varType v) == deBruijnize multiplicityTy

--pprT :: Outputable a => a -> Text
--pprT = T.pack . showPprUnsafe

--printP :: (MonadIO m, Outputable a) => a -> m ()
--printP = liftIO . putStrLn . showPprUnsafe

--printPretty :: (MonadIO m, Show a, Pretty a) => Doc Void -> a -> m ()
--printPretty str a = liftIO $ do
--  putStrLn ""
--  print str
--  putStr (replicate 4 ' ')
--  print $ pretty a
--  print a
--  putStrLn ""

---- -- | We use a dummy var for type variables in the context, so ocurrences of type can refer to them? or do we just delete all ocurrences of Type expressions that are not-mult variables?
---- dummyVar
--instance MonadFail CoreM where
--  fail = error
