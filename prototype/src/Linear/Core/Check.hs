{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
module Linear.Core.Check where

-- import Debug.Trace
import Data.List ((\\))
import Data.Maybe
import qualified Data.Map as M
import Data.Functor.Foldable
import Control.Monad.State
import Control.Monad.Except
import Control.Monad
import Control.Applicative
-- import Data.Set (Set)
import qualified Data.Set as S
-- import Data.Text (Text)
import qualified Data.Text as T
import Prettyprinter
import Data.Void
-- import Error.Diagnose

import Linear.Core.Syntax
import GHC.Driver.Ppr (showPprUnsafe)
import GHC.Plugins (literalType)

{-
Notes:

* For now we don't do good error reporting (perhaps we could use diagnose?!)
* We use Input/Output context to track linear variables without context splitting
* I'm missing the rule for Var_p

* We don't allow multiplicity variables to appear anywhere besides function
types, so we don't need a type-level multiplicity variable

------

* Checking types after translation from Core is anything but trivial, because
the conversion is very lossy - we lose casts, coercions, type constructors,
type variables, synonyms, etc...

* Therefore, we no longer check types. Type checking is already done by the Core typechecker

* Instead, we only check that linearity is maintained and ignore the types.

-}

newtype Check a = Check {unCheck :: StateT Ctx (Except (Doc Void)) a} -- romes:Todo: Except (Diagnostic Text)
  deriving (Functor, Applicative, Monad, MonadState Ctx, MonadError (Doc Void), Alternative)

instance MonadFail Check where
  fail txt = throwError (pretty txt)

runClosedCheck :: Check a -> Either (Doc Void) a
runClosedCheck check = runExcept do
  (a,ctx) <- runStateT (unCheck check) mempty
  unless (null $ projectCtxLinear ctx) (throwError "Linear variables escaped")
  return a

runCheck :: Ctx -> Check a -> Either (Doc Void) a
runCheck ctx check = runExcept do
  (a,ctx') <- runStateT (unCheck check) ctx
  unless (projectCtxLinear ctx' == projectCtxLinear ctx) (throwError "Linear variables escaped")
  return a

-- TODO: Should project linear also return x{:}_p ?
projectCtxLinear :: Ctx -> [Name]
projectCtxLinear = M.keys . M.filter (\case Id _ (LambdaBound One) _ -> True; _ -> False)

projectLinear :: [Var] -> [Var]
projectLinear = filter (\case Id _ (LambdaBound One) _ -> True; _ -> False)

-- | Use a variable from the environment.
-- If it is a linearly-bound variable it will be consumed (and no longer available in the context)
-- It returns the used variable
--
-- We pass Right name if the variable is definitely in scope (we might not have
-- the full variable but know it is in scope, e.g. if the variable occurs in the
-- delta environment), and Left var if
-- we're unsure (the reason for using Var instead of just Name is that this
-- might be a free variable defined in another module - therefore we need it
-- whole to be able to return it (otherwise we won't be able to discover the
-- type of that free variable))
use :: Either Var Name -> Check Var
use evar = do
  let name = case evar of
               Right n  -> n
               Left var -> varName var
  mvar <- gets (M.lookup name)
  case mvar of
    Nothing -> case evar of
                 Left var -> return var -- aren't sure whether this is bound, so returning var here (unless something is terribly wrong) means this is a top-level free variable
                 Right _  -> throwError ("Wasn't able to find variable that was definitely bound in scope:" <+> pretty name)
    Just var -> do
      case var of
        Id' var ->
          case idBinding var of
            LambdaBound Many -> pure ()
            LambdaBound One -> do
              modify (M.delete name)
            LambdaBound (MV' _) -> do
              -- We must treat polymorphic variables as if they were linear, bc
              -- they might be instantiated to 'One' later on.
              modify (M.delete name)
            DeltaBound ue -> do
              mapM_ (use . Right) (S.toList ue) -- all elements should already have mult == One.
        MultVar' _ ->
          pure ()
      return var

extend :: Var -> Check a -> Check a
extend var check = do
  modify (M.insert (varName var) var)
  a <- check
  case var of
    MultVar _ -> return a
    Id _ bnd name -> case bnd of
      LambdaBound One -> do
        True <- wasConsumed name
        return a
      LambdaBound (MV' _) -> do
        True <- wasConsumed name
        return a
      LambdaBound Many -> do
        -- Unr. vars don't escape their scope
        modify (M.delete name)
        return a
      DeltaBound _ue -> do
        -- Is this true?: and <$> mapM wasConsumed (projectLinear ue) >>= assert

        -- Δ-vars don't escape their scope
        modify (M.delete name)
        return a
  where
    wasConsumed x = isNothing <$> gets (M.lookup x)

extends :: [Var] -> Check a -> Check a
extends vars check = foldl (flip extend) check vars

-- | @substTy π n σ@ performs the substitution σ[π/n]
substTy :: Mult -> Name -> Ty -> Ty
substTy m name = \case
  Datatype n' mults -> Datatype n' (map (substMult m name) mults)
  FunTy   t1  m' t2 -> FunTy (substTy m name t1) (substMult m name m') (substTy m name t2)
  Scheme  n' t1 -> if n' == name then Scheme n' t1 else Scheme n' (substTy m name t1)

substMult :: Mult -> Name -> Mult -> Mult
substMult m name = \case
  One -> One
  Many -> Many
  MV n' -> if n' == name then m else MV n'

-- | Asserts the input and output environments of a type-checking computation are the same
-- i.e. no linear variables were consumed
usesNoLinearVariables :: Check a -> Check a
usesNoLinearVariables check = do
  prev <- get
  a <- check
  after <- get
  when (prev /= after) $
    throwError "Linear variables were consumed more than once (likely an unrestricted function was applied to an argument that uses linear variables, thereby consuming them unrestrictedly)"
  return a

-- | Runs a 'Check' action under some context, and restore the context after
-- the action is run. Additionally, it outputs the linear variables used in the
-- given 'Check' action
dryRunUsed :: Check a -> Check (a, UsageEnv)
dryRunUsed check = do

    -- Get the original context
    _Γ_Δ <- get
    let _Δ = projectCtxLinear _Γ_Δ

    -- The "dry-run" action
    a <- check

    -- The output linear context
    _Δ' <- gets projectCtxLinear

    -- The linear variables used to run the 'Check' action
    let usedΔ = S.fromList (_Δ \\ _Δ')

    -- Restore the context
    put _Γ_Δ

    return (a, usedΔ)

-- | We type-check elaborated Core expressions after every optimising
-- transformation.
--
-- We can also run this function on the output of the type-inference that
-- transforms Expr Name -> CoreExpr to validate it.
--
-- The function performs some additional checks regarding validity of binders
-- and linearity and such, in contrast to 'infer' -- and can also work on the
-- expressions constructed by infer (i.e. fully annotated expressions)
--
-- More importantly, infer doesn't check linearity directly! For the purpose of
-- the prototype it isn't necessary (no good error reporting). It infers a type
-- with the linearity given by the annotations, then calls this function on its
-- result :D.
typecheck :: CoreExpr -> Check (CoreExpr, Ty)
typecheck = cata \case
  LitF (L lit) -> return (Lit (L lit), Datatype (T.pack $ showPprUnsafe $ literalType lit) [])

  --- * (Var_π)
  VarF (MultVar _) -> error "impossible"

  --- * (Var_ω) and (Var_1)
  VarF v@Id{} -> do
    Id' id <- use (Left v)
    -- TODO assert var matches one found in environment?
    return (Var (Id' id), varType id)

  --- * (->I) and (∀I)
  LamF var e -> do
    (e, t) <- extend var e
    case var of

      --- ** (∀I)
      MultVar n -> return (Lam var e, Scheme n t)

      --- ** (->I)
      Id _ (DeltaBound _) _ -> error "impossible"
      Id vt (LambdaBound m) _ ->
        return (Lam var e, FunTy vt m t)

  --- * (->E) and (∀E)
  AppF e1 e2       -> do
    (e1,t1) <- e1
    case t1 of
      --- ** (∀E)
      Scheme n schemet -> do
        (Mult m,Datatype "Mult" []) <- e2 -- built-in "Mult" kind to "kindcheck" multiplicities
        return (App e1 (Mult m), substTy m n schemet)

      --- ** (->E)
      FunTy argt m rett -> do
        case m of

          --- *** (->E_1)
          One  -> do
            (e2,t2) <- e2
            checkEqTy argt t2
            return (App e1 e2, rett)

          --- *** (->E_p)
          MV _ -> do
            -- just as above
            (e2,t2) <- e2
            checkEqTy argt t2
            return (App e1 e2, rett)

          --- *** (->E_ω)
          Many -> do
            (e2,t2) <- usesNoLinearVariables e2
            checkEqTy argt t2
            return (App e1 e2, rett)
      _ -> empty

  -- we don't consider type-lets in our system (yet?)
  LetF (NonRec (MultVar _) _) _ -> throwError "We don't yet support type-level lets"

  --- * (Let)
  LetF (NonRec id@(Id var_ty var_bndr _) e) e' -> do
    {-

    (1) The things that were used to typecheck $e$ were restored to typecheck $e'$,
    because let-binding doesn't consume variables, only using the bound
    variables does.

                    Γ;Δ/Δ'⊦e:σ   Γ;Δ,x/Δ''⊦e':φ 
                    ---------------------------
                      Γ;Δ/Δ''⊦let x=e in e':φ

    The output will always contain all the unrestricted variables in the input, so
    we can conceptually separate them in the rule, despite in practice them being
    together

    -}

    -- The things that are used to typecheck $e$ are restored (1)
    ((e, t), varΔ) <- dryRunUsed (typecheck e)

    unless (t == var_ty) $
      throwError "Type of binder doesn't match the type of the body of the binder"

    unless (DeltaBound varΔ == var_bndr) $
      throwError "Usage env. of variable doesn't match linear variables used to type the body of its binder, binder is incorrectly annotated!"

    (e', t') <- extend id e'

    return (Let (NonRec id e) e', t')
    
  --- * (Let)
  LetF (Rec bndrs) e' -> do

    {-

    (1) This rule assumes the recursive definitions form a strongly connected component

    (2) For recursive binders, inferring the usage environment is much
    harder. For 'Check' we assume they're correct, and infer them at another stage.

    (3) We typecheck all binder bodies, requiring that they all use the same linear resources

    (4) We restore the original linear resources to check e'

              {Γ;Δ,{xΔ}/Δ'⊦e:σ}   Γ;Δ,{xΔ}/Δ''⊦e':φ   all_eq {Δ'}
              ---------------------------------------------------
                      Γ;Δ/Δ''⊦let rec {xΔ=e} in e':φ

    The output will always contain all the unrestricted variables in the input, so
    we can conceptually separate them in the rule, despite in practice them being
    together

    -}

    let (bndr_vars, bndr_bodies) = unzip bndrs
        !bndr_ids = map varId bndr_vars

    -- TODO: assert all var-envs. are the same

    (es,tys,ds) <- unzip3 <$> forM bndr_bodies \bndr_body -> do
      ((e,t),d) <- dryRunUsed (extends bndr_vars (typecheck bndr_body))
      return (e,t,d)

    unless (tys == map varType bndr_ids) $
      throwError "Expecting the types of the binders and their bodies to be the same"

    unless (map DeltaBound ds == map idBinding bndr_ids) $
      throwError "Expecting the usage environments of all let-rec binders to be the same as their bodies"

    unless (allEq ds) $
      throwError "Expecting all let-rec binder bodies to use the same linear variables"

    (e', t') <- extends bndr_vars e'

    return (Let (Rec (zip bndr_vars es)) e', t')

  -- TODO: Should the var have just one DeltaEnv, like (1) Δ_s, and then when
  -- passed to the alternatives is changed, (2) or all of them (costly?), or
  -- (3) None, so that it is more principled in the sense "the u.e. for
  -- case-vars are computed during the case? For now, we do opt 1, seems good since the env. of $e$ is the hardest to compute, the others are trivial?
  CaseF scrut var alts -> do
    {-


          Γ;Δ/Δ'⊦e:σ   {Γ;Δ',z/Δ''⊦ρ -> e':σ => φ} 
          ----------------------------------------
            Γ;Δ/Δ''⊦case e of z { {ρ -> e'} } :φ


    -}

    _Δ  <- gets projectCtxLinear
    (scrut, t) <- scrut
    _Γ_Δ' <- get

    let _Δ'  = projectCtxLinear _Γ_Δ'
        _Δ_s = S.fromList (_Δ \\ _Δ')

    unless (t == varType (varId var)) $
      throwError "The type of the case var doesn't match the type of the scrutinee"

    unless (Just _Δ_s == varUE var) $
      throwError "The usage env. of the case var doesn't match the one required to typecheck the scrutinee"

    -- IMPORTANT:TODO: Must handle EmptyCase!!!

    alts_res <- forM alts $ \alt -> do
      -- The same environment is used to typecheck all alternatives
      put _Γ_Δ'
      case alt of
        (Alt DEFAULT [] ei) -> do
          (ei, t') <- extend var (typecheck ei) -- the var has the usage env. of the scrutinee
          _Δ'' <- gets projectCtxLinear
          return (Alt DEFAULT [] ei, t', _Δ' \\ _Δ'')
        (Alt DEFAULT _bs _ei) -> throwError "How can the default alternative bind any variables? We could likely enforce this in the types"
        (Alt con bs ei) -> do
          (ei, t') <- extend (var `setUE` S.fromList (map varName (projectLinear bs))) $ extends bs (typecheck ei)
          _Δ'' <- gets projectCtxLinear
          return (Alt con bs ei, t', _Δ' \\ _Δ'')

    let (alts', tys, usedVars) = unzip3 alts_res

    unless (allEq tys) $
      throwError "The type of every alternative must be the same"

    unless (allEq usedVars) $
      throwError "The linear variables used by every alternative must be the same"

    return (Case scrut var alts', head tys)

  MultF One  -> return (Mult One, Datatype "Mult" [])
  MultF Many -> return (Mult Many, Datatype "Mult" [])
  MultF (MV m) -> do
    Just _ <- gets (M.lookup m)
    return (Mult (MV m), Datatype "Mult" [])

  AnnF _ _ -> throwError "Annotated terms shouldn't occur in the elaborated Linear Core program"

-- exprTy :: CoreExpr -> Ty
-- exprTy = cata undefined

-- Note! We don't check types because of the elaborate types in Core in comparison to Linear (mini) Core.
-- This is a noop now.
checkEqTy :: Ty -> Ty -> Check ()
checkEqTy _ _ = pure ()
-- checkEqTy t1 t2 = if t1 == t2 then pure ()
--                               else throwError $ "Expecting" <+> pretty t1 <+> "and" <+> pretty t2 <+> "to match."

allEq :: Eq a => [a] -> Bool
allEq = allEq' Nothing where
  allEq' _        []     = True
  allEq' Nothing  (x:xs) = allEq' (Just x) xs
  allEq' (Just y) (x:xs) = x == y && allEq' (Just y) xs
