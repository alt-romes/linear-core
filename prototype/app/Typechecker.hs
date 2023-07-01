{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
module Typechecker where

import Data.Maybe
import qualified Data.Map as M
import Data.Functor.Foldable
import Control.Monad.State
import Control.Monad.Except
import Control.Monad
import Syntax
import Control.Applicative (empty)

{-
Notes:

* For now we don't do good error reporting
* We use Input/Output context to track linear variables without context splitting
* I'm missing the rule for Var_p

* We don't allow multiplicity variables to appear anywhere besides function
types, so we don't need a type-level multiplicity variable
-}

type Check = StateT Ctx Maybe

runClosedCheck :: Check a -> Maybe a
runClosedCheck check = do
  (a,ctx) <- runStateT check mempty
  when (not $ null $ M.elems $ M.filter (\case Id _ (LambdaBound One) _ -> True; _ -> False) ctx) (fail "Linear variables escaped")
  return a

projectLinear :: UsageEnv -> [Name]
projectLinear = M.keys . M.filter (== One)

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
          _ <- mapM use (projectLinear ue) -- all elements should already have mult == One.
          pure ()
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
      LambdaBound Many -> return a
      DeltaBound ue -> do
        True <- all id <$> mapM wasConsumed (projectLinear ue)
        return a
  where
    wasConsumed x = isNothing <$> gets (M.lookup x)

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

-- Lam (Id (Datatype "A" [MV "p"]) (LambdaBound (MV "p")) "x") $
--   Var (Id (Datatype "A" [MV "p"]) (LambdaBound (MV "p")) "x")
typecheck :: CoreExpr -> Check (CoreExpr, Ty)
typecheck = cata \case
  VarF (MultVar _) -> error "impossible"
  VarF (Id _ _ name) -> do
    Id' id <- use name
    -- TODO: Perhaps assert var matches one found in environment?
    return (Var (Id' id), varType id)
  LamF var e -> do
    (e, t) <- extend var e
    case var of
      MultVar n -> return (Lam var e, Scheme n t)
      Id _ (DeltaBound _) _ -> error "impossible"
      Id vt (LambdaBound m) _ ->
        return (Lam var e, FunTy vt m t)
  AppF e1 e2       -> do
    (e1,t1) <- e1
    case t1 of
      Scheme n schemet -> do
        (Mult m,Datatype "Mult" []) <- e2 -- built-in "Mult" kind to "kindcheck" multiplicities
        return (App e1 (Mult m), substTy m n schemet)
      FunTy argt m rett -> do
        case m of
          One  -> do
            (e2,t2) <- e2
            checkEqTy argt t2
            return (App e1 e2, rett)
          MV _ -> do
            -- just as above
            (e2,t2) <- e2
            checkEqTy argt t2
            return (App e1 e2, rett)
          Many -> do
            (e2,t2) <- usesNoLinearVariables e2
            checkEqTy argt t2
            return (App e1 e2, rett)
      _ -> empty
  LetF bind _      -> undefined
  CaseF _ var alts -> undefined
  MultF One  -> return (Mult One, Datatype "Mult" [])
  MultF Many -> return (Mult One, Datatype "Mult" [])
  MultF (MV m) -> do
    Just _ <- gets (M.lookup m)
    return (Mult (MV m), Datatype "Mult" [])

exprTy :: CoreExpr -> Ty
exprTy = cata undefined


checkEqTy :: Ty -> Ty -> Check ()
checkEqTy t1 t2 = if t1 == t2 then pure () else fail $ "Expecting " ++ show t1 ++ " and " ++ show t2 ++ " to match."

