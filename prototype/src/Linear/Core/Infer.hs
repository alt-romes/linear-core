{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE BlockArguments #-}
{-|

Based on "Bidirectional Typing" by JANA DUNFIELD and NEEL KRISHNASWAMI:
https://dl.acm.org/doi/pdf/10.1145/3450952

Perhaps this would all be easier accounting for linearity using the rules in Sec. 6?

-}
module Linear.Core.Infer where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map as M
import Prelude hiding (lookup)
import Linear.Core.Syntax
import Data.Functor.Foldable
import Control.Monad.Reader
import Control.Monad.Except
import Control.Applicative

import Data.Void
import Prettyprinter

-- We run 'typecheck' after the naive inference, to check linearity and validation.
import qualified Linear.Core.Check as Core

-- We don't have SrcSpans yet, for reporting error messages.

newtype Infer a = Infer { unInfer :: ReaderT Ctx (Except (Doc Void)) a }
  deriving (Functor, Applicative, Monad, MonadReader Ctx, MonadError (Doc Void), Alternative)

instance MonadFail Infer where
  fail txt = throwError (pretty txt)

runClosedInfer :: Infer a -> Either (Doc Void) a
runClosedInfer action = runExcept (runReaderT (unInfer action) mempty)

err :: Doc Void -> Infer a
err = throwError

lookup :: Name -> Infer Var
lookup n = asks (M.lookup n) >>=
  \case Nothing -> err $ "Variable " <> pretty n <> " is not in scope."
        Just v  -> return v

extend :: Name -> Var -> Infer a -> Infer a
extend n v syn = do
  asks (M.lookup n) >>=
    \case Just _  -> err $ "Variable" <+> pretty n <+> "is already in scope! We don't support shadowing."
          Nothing -> pure ()
  local (M.insert n v) syn

synth :: Expr Name -> Infer (CoreExpr, Ty)
synth = \case
  Var n -> do
    Id ty binding name <- lookup n
    return (Var (Id ty binding name), ty)

  App f arg -> do
    (fc, ft) <- synth f
    case ft of
      FunTy argty _ resty -> do
        (argc, _) <- check arg argty
        return (App fc argc, resty)
      _ -> err $ "Applying non-function to an argument in:" <+> hang 4 (pretty $ App f arg)

  Mult m ->
    case m of
      MV v ->
        do MultVar v' <- lookup v -- check if is bound
           unless (v' == v) $ err "This shouldn't be possible, how did we mix /that/ up?"
           return (Mult m, Datatype "Mult" [])
      _ -> return (Mult m, Datatype "Mult" [])
  Ann e t -> do
    check e t

  -- l@Lam{}  -> err $ "Lambda abstractions aren't inferrable, if you get this error you are likely missing a type annotation on a function." <> hang 4 (pretty l)
  -- l@Let{}  -> err $ "Let expressions aren't inferrible:" <+> hang 4 (pretty l)
  -- c@Case{} -> err $ "Case expressions aren't inferrible:" <+> hang 4 (pretty c)
  other -> err $ "Couldn't find a type for" <+> parens (pretty other) <> ". Try adding a type annotation."


check :: Expr Name -> Ty -> Infer (CoreExpr, Ty)
check (Lam b e) (FunTy arg m ret)
  = do
    let idx = Id arg (LambdaBound m) b
    (e',_) <- extend b idx $ check e ret
    return (Lam idx e', FunTy arg m ret)
check (Let (NonRec x e) body) ty
{-
             Γ ⊦ e => A    Γ,x:A ⊦ e' <= B
            -------------------------------
               Γ ⊦ let x = e in e' <= B
-}
  = do
    (e',ety) <- synth e
    let idx = Id ety (DeltaBound mempty) x -- TODO: DELTA ENVIRONMENT! Needss Resources Monad factored out
    (body', bty) <- extend x idx $ check body ty
    return (Let (NonRec idx e') body', bty)

    -- darn, we need the usage environment here.
check (Let (Rec _) e) _ = err "Recursive let inference not implemented yet" -- TODO: how exactly?

check (Case scrut name alts) ty
{-
           Γ ⊦ e => A    Γ,x:A ⊦ e' <= B
          -------------------------------
             Γ ⊦ let x = e in e' <= B
-}
  = undefined

check other ty
{-
We can change from checking back to synthesizing when inference synthesizes the type we're checking against.

            Γ ⊦ e => A   A = B
            -------------------
               Γ ⊦ e <= B
-}
  = do
    (other', ty') <- synth other
    if ty == ty'
       then return (other', ty')
       else err $ "Checking that" <+> parens (pretty other) <+> "has type" <+> parens (pretty ty) <> ", but instead inferred" <+> parens (pretty ty')



-- data Expr b where
--   Var  :: b -> Expr b -- Only term variables and constructors. Type variables at the term level would be (Ty (TyMultVar "p"))
--   Lam  :: b -> Expr b -> Expr b
--   App  :: Expr b -> Expr b -> Expr b
--   Let  :: Bind b -> Expr b -> Expr b
--   Case :: Expr b -> b -> [Alt b] -> Expr b
--   Mult :: Mult -> Expr b
--   Ann  :: Expr b -> Ty -> Expr b

