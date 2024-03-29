{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Translate.Test where
import Data.Either
import qualified Data.Map as M
import Error.Diagnose
import qualified Data.Text as T

import Data.Text (Text)
import Test.Tasty
import Test.Tasty.HUnit

import Prettyprinter

import Linear.Core.Translate.Syntax
import Linear.Core.Translate.Parser
import Linear.Core.Translate.Check
import Linear.Core.Translate.Infer

-- Let's try writing a simple program like id @A
-- id :: ∀ p. (A p) ->p (A p)
-- id = /\p. \x:_pA -> x:A
idProg :: CoreTerm
idProg
  = Term
    (M.singleton "MkA" (Id (Scheme "kp" (Datatype "A" [MV "p"])) (DeltaBound mempty) "MkA"))
    (Lam (MultVar "p") $
       Lam (Id (Datatype "A" [MV "p"]) (LambdaBound (MV "p")) "x") $
         Var (Id (Datatype "A" [MV "p"]) (LambdaBound (MV "p")) "x")
    )
    (Scheme "p" (FunTy (Datatype "A" [MV "p"]) (MV "p") (Datatype "A" [MV "p"])))

id2 :: CoreExpr
id2 =
 Lam (Id (Datatype "A" [MV "p"]) (LambdaBound (MV "p")) "x") $
   Var (Id (Datatype "A" [MV "p"]) (LambdaBound (MV "p")) "x")

idBad :: CoreExpr
idBad =
 Lam (Id (Datatype "A" [MV "p"]) (LambdaBound (MV "p")) "x") $
   Var (Id (Datatype "A" [MV "p"]) (LambdaBound (MV "p")) "y")


parsingTests :: TestTree
parsingTests = testCase "Parsing some things" $ do

  assertBool "Parse K @1" $ parses "K @1"
  assertBool "Parse K @ω" $ parses "K @ω"
  assertBool "Parse λp -> K @p" $ parses "λp -> K @p"
  assertBool "Parse T4" $ parses "\\x -> case x of z {Nothing -> True; Just y -> y}"
  assertBool "Parse T5" $ parses "\\p -> \\x -> x"
  assertBool "Parse T6" $ parses "\\x -> case x of z { Nothing -> True; Just y -> not (and y z) }"
  assertBool "Parse T7" $ parses "(λz -> (λx -> z x) (λy -> y))"
  assertBool "No Parse T8" $ not $ parses "(z -> (λx -> z x) (λy -> y))"
  assertBool "Parse T9" $ parses "λx -> case not x of z { True -> False; False -> True }"
  assertBool "Parse T10" $ parses "λx -> case testytest (not (not x)) of z { K a b c d -> tuple a b c d }"

  assertBool "Parse ann1" $ parses "λp -> λx -> x :: forall p. A %p -> A"
  parse "λp -> λx -> x :: forall p. A %p -> A" @?= Lam "p" (Lam "x" (Ann (Var "x") (Scheme "p" (FunTy (Datatype "A" []) (MV "p") (Datatype "A" [])))))

  assertBool "Parse ann2" $ parses "(λp -> λx -> x) :: forall p. A %p -> A"
  parse "(λp -> λx -> x) :: ∀ p. A %p -> A" @?= Ann (Lam "p" (Lam "x" (Var "x"))) (Scheme "p" (FunTy (Datatype "A" []) (MV "p") (Datatype "A" [])))

  assertBool "Parse ann3" $ parses "(λx -> let y = K x x :: KT 1 ω in y)"
  parse "(λx -> let y = K x x :: KT 1 ω in y)" @?= Lam "x" (Let (NonRec "y" (Ann (App (App (Var "K") (Var "x")) (Var "x")) (Datatype "KT" [One,Many]))) (Var "y"))

  where
    parses = isRight . parseExpr
    parse :: Text -> Expr Name
    parse = fromRight (error "no parse") . parseExpr

prettyTests :: TestTree
prettyTests = testCase "Pretty printing and round tripping" $ do

  -- These aren't "true" roundtrips, but are good enough.
  assertBool "Roundtrips K @1" $ roundtrips "K @1"
  assertBool "Roundtrips K @ω" $ roundtrips "K @ω"
  assertBool "Roundtrips λp -> K @p" $ roundtrips "λp -> K @p"
  assertBool "Roundtrips T4" $ roundtrips "λx -> case x of z { Nothing -> True; Just y -> y; }"
  assertBool "Roundtrips T5" $ roundtrips "λp -> λx -> x"
  assertBool "Roundtrips T6" $ roundtrips "λx -> case x of z { Nothing -> True; Just y -> not (and y z); }"
  assertBool "Roundtrips T7" $ roundtrips "λz -> (λx -> z x) (λy -> y)"
  assertBool "Roundtrips T9" $ roundtrips "λx -> case not x of z { True -> False; False -> True; }"
  assertBool "Roundtrips T10" $ roundtrips "λx -> case testytest not (not x) of z { K a b c d -> tuple a b c d; }"
  assertBool "Roundtrips T11" $ roundtrips "λx -> let y = K x x :: KT 1 ω in y"
  where
    roundtrips x = case parseExpr x of
                     Right expr -> T.pack (show (Prettyprinter.group $ pretty expr)) == x
                     Left _ -> error "don't test this here"

inferTests :: TestTree
inferTests = testCase "Bidirectional type checking/inference tests" $ do

  assertBool "Infer 0" $ infers "(λk -> λign -> k) :: A -o B -o A"

  assertBool "Infer 1" $ not $ infers "λx -> let y = K x x :: KT 1 ω in y" -- its a lambda, shouldn't work.

  assertBool "Infer 2" $ infers "(λf -> λx -> let y = f x x :: KT 1 ω in y) :: (A -o A -o KT 1 ω) -> A -> KT 1 ω"
  
  assertBool "Infer 3" $ infers "(λf -> λx -> let y = f x x :: KT 1 ω in y) :: (A -o A -o KT 1 ω) -> A -o KT 1 ω" -- wrong linearity, this shouldn't typecheck.

  -- assertBool "Infer 3" $ not (typechecks idBad)

  where
    infers = isRight . runClosedInfer . synth . fromRight (error "in infers") . parseExpr
    infer = fromRight (error "in infer 1") . runClosedInfer . synth . fromRight (error "in infer 2") . parseExpr

-- For interactive use
_infer :: Text -> IO ()
_infer t = do
  case parseExpr t of
    Left b -> print b
    Right p -> case runClosedInfer $ synth p of
                 Left b -> print b
                 Right x -> print (pretty x)

typecheckingTests :: TestTree
typecheckingTests = testCase "Typecheck some things" $ do

  assertBool "Typechecking idProg" $ typechecks (erase idProg)

  assertBool "Typechecking id2" $ typechecks id2

  assertBool "Shouldn't typecheck idBad" $ not (typechecks idBad)

  where
    typechecks = isRight . runClosedCheck . typecheck

main :: IO ()
main = defaultMain $ testGroup "Tests"
  [ parsingTests
  , prettyTests
  , inferTests
  , typecheckingTests
  ]


instance Show (Diagnostic Text) where
  show d = show (prettyDiagnostic True 4 d)
