import Data.Maybe
import qualified Data.Map as M

import Test.Tasty
import Test.Tasty.HUnit

import Linear.Core.Syntax
import Linear.Core.Check

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

main :: IO ()
main = defaultMain $
  testCase "Typecheck some things" $ do

    -- 2 + 2 @?= 4

    assertBool "Typechecking idProg" $ typechecks (erase idProg)

    assertBool "Typechecking id2" $ typechecks id2

    assertBool "Shouldn't typecheck idBad" $ (typechecks idBad)

  where
    typechecks = isJust . runClosedCheck . typecheck

