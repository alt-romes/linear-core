{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
module Linear.Core.Check where

import Data.List ((\\))
import Data.Maybe
import qualified Data.Map as M
import Data.Functor.Foldable
import Control.Monad.State
import Control.Monad.Except
import Control.Monad
import Control.Applicative (empty)
import Data.Set (Set)
import qualified Data.Set as S

import Linear.Core.Syntax

{-
Notes:

* For now we don't do good error reporting (perhaps we could use diagnose?!)
* We use Input/Output context to track linear variables without context splitting
* I'm missing the rule for Var_p

* We don't allow multiplicity variables to appear anywhere besides function
types, so we don't need a type-level multiplicity variable
-}

type Check = StateT Ctx Maybe

runClosedCheck :: Check a -> Maybe a
runClosedCheck check = do
  (a,ctx) <- runStateT check mempty
  unless (null $ projectCtxLinear ctx) (fail "Linear variables escaped")
  return a

-- TODO: Should project linear also return x{:}_p ?
projectCtxLinear :: Ctx -> [Name]
projectCtxLinear = M.keys . M.filter (\case Id _ (LambdaBound One) _ -> True; _ -> False)

-- | Use a variable from the environment.
-- If it is a linearly-bound variable it will be consumed (and no longer available in the context)
use :: Name -> Check Var
use name = do
  Just var <- gets (M.lookup name)
  case var of
    Id' var ->
      case idBinding var of
        LambdaBound Many -> pure ()
        LambdaBound One -> do
          modify (M.delete name)
        LambdaBound (MV' _) -> do
          -- ROMES:TODO: I suppose we must treat polymorphic variables as if
          -- they were linear, bc they might be instantiated to 'One' later on.
          modify (M.delete name)
        DeltaBound ue -> do
          mapM_ use (S.toList ue) -- all elements should already have mult == One.
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
      DeltaBound ue -> do
        -- Is this true?: and <$> mapM wasConsumed (projectLinear ue) >>= assert

        -- Δ-vars don't escape their scope
        modify (M.delete name)
        return a
  where
    wasConsumed x = isNothing <$> gets (M.lookup x)

extends :: [Var] -> Check a -> Check a
extends [] check = check
extends (var:vars) check = extends vars $ extend var check

-- | @substTy π n σ@ performs the substitution σ[π/n]
substTy :: Mult -> Name -> Ty -> Ty
substTy m name = \case
  -- TyMultVar n' -> if n' == name then Mult m else TyMultVar n'
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
    fail "Linear variables were consumed more than once (likely an unrestricted function was applied to an argument that uses linear variables, thereby consuming them unrestrictedly)"
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

typecheck :: CoreExpr -> Check (CoreExpr, Ty)
typecheck = cata \case

  --- * (Var_π)
  VarF (MultVar _) -> error "impossible"

  --- * (Var_ω) and (Var_1)
  VarF (Id _ _ name) -> do
    Id' id <- use name
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
  LetF (NonRec (MultVar n) _) e' -> fail "We don't yet support type-level lets"

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
      fail "Type of binder doesn't match the type of the body of the binder"

    unless (DeltaBound varΔ == var_bndr) $
      fail "Usage env. of variable doesn't match linear variables used to type the body of its binder, binder is incorrectly annotated!"

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
      fail "Expecting the types of the binders and their bodies to be the same"

    unless (map DeltaBound ds == map idBinding bndr_ids) $
      fail "Expecting the usage environments of all let-rec binders to be the same as their bodies"

    unless (allEq ds) $
      fail "Expecting all let-rec binder bodies to use the same linear variables"

    (e', t') <- extends bndr_vars e'

    return (Let (Rec (zip bndr_vars es)) e', t')

  CaseF _ var alts -> undefined
  MultF One  -> return (Mult One, Datatype "Mult" [])
  MultF Many -> return (Mult Many, Datatype "Mult" [])
  MultF (MV m) -> do
    Just _ <- gets (M.lookup m)
    return (Mult (MV m), Datatype "Mult" [])

exprTy :: CoreExpr -> Ty
exprTy = cata undefined

checkEqTy :: Ty -> Ty -> Check ()
checkEqTy t1 t2 = if t1 == t2 then pure () else fail $ "Expecting " ++ show t1 ++ " and " ++ show t2 ++ " to match."

allEq :: Eq a => [a] -> Bool
allEq = allEq' Nothing where
  allEq' _        []     = True
  allEq' Nothing  (x:xs) = allEq' (Just x) xs
  allEq' (Just y) (x:xs) = x == y && allEq' (Just y) xs
