{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE PatternSynonyms #-}
module Syntax where

import Data.Map (Map)
-- import qualified Data.Map as M
-- import Data.IntMap (IntMap)
-- import qualified Data.IntMap as IM

{-
Notes

* No Mult in Scheme, we use DeBruijn numbering

* After looking at type systems and proofs on Agda, Haskell almost looks untyped :)

* We use Lam with 'Var' as in GHC.Core, where 'Var' can be either a type or term
variable (we don't have meta ty vars)

* Unlike CoreExpr, however, we distinguish between tyvars and ids using different
types, instead of by type synonyms

* Never thought about how DeBruijn is with let (rec) bindings

* It's about time I write a renaming pass, for now assume no shadowing

* We don't account for GADTs.

* We need to validate the datatype Name + Mults against the Name definition and the Mults it is actually expecting
-}

type Name = String

data Id = MkId { varType   :: Ty
               , idBinding :: IdBinding
               , varName   :: Name
               }
newtype MultVar = MkMultVar { varName :: Name }

data Var = Id' Id
         | MultVar' MultVar
{-# COMPLETE Id, MultVar #-}

pattern Id :: Ty -> IdBinding -> Name -> Var
pattern Id ty binding name = Id' (MkId ty binding name)

pattern MultVar :: Name -> Var
pattern MultVar name = MultVar' (MkMultVar name)

data Mult = Many       -- ω
          | One        -- 1
          | MV' MultVar -- π

pattern MV :: Name -> Mult
pattern MV name = MV' (MkMultVar name)

type UsageEnv = Map Name Mult

data IdBinding = LambdaBound Mult
               | LetBound UsageEnv
               | CaseBound [UsageEnv] -- One UE per alternative

data Ty
  = Datatype Name [Mult]    -- K π_1 ... π_n
  | FunTy   Ty   Mult Ty    -- φ ->π σ
  | Scheme  Name Ty         -- ∀p. φ

data Expr
  = Var Var
  | Lam Var Expr
  | App Expr Expr
  | Let Bind Expr
  | Case Expr Var [Alt]
  | Ty Ty

data Bind = NonRec Var Expr
          | Rec [(Var, Expr)]

data Alt
    = Alt AltCon [Var] Expr

data AltCon
  = DataAlt DataCon   --  ^ A plain data constructor: @case e of { Foo x -> ... }@.
                      -- Invariant: the 'DataCon' is always from a @data@ type, and never from a @newtype@

  | DEFAULT           -- ^ Trivial alternative: @case e of { _ -> ... }@

-- | All constructors are of the form K~\overline{x{:}_\pi\sigma}
-- We record the information about the multiplicity and type of each argument
-- to the constructor. No existentials, but a datatype may be parametrized by
-- mult. variables.
data DataCon
  = DataCon { dcName :: Name
            , dcUnivMultVars :: [Mult]
            , dcArgTys :: [Scaled Ty]
            }

data Scaled a = Scaled !Mult a

type Ctx = [Var]
-- ^ The context is a list of variables that can be
-- * Lambda bound vars (x :_π σ)
-- * Let bound vars    (x :_Δ σ)
-- * Case bound vars   (x :_\ov{Δ} σ)
-- * Mult vars         (π)
-- * DataCons          (K:σ), which are really just a special sort of top-level closed-Δ let-bound vars (K :_\ov{\cdot} σ)

-- | Γ |- e : τ
data Term = Term Ctx Expr Ty


-- Let's try writing a simple program like id @A
-- id :: ∀ p. (A p) ->p (A p)
-- id = /\p. \x:_pA -> x:A
idProg :: Term
idProg
  = Term
    [Id (Scheme "kp" (Datatype "A" [MV "p"])) (LetBound mempty) "MkA"]
    (Lam (MultVar "p") $
       Lam (Id (Datatype "A" [MV "p"]) (LambdaBound (MV "p")) "x") $
         Var (Id (Datatype "A" [MV "p"]) (LambdaBound (MV "p")) "x")
    )
    (Scheme "p" (FunTy (Datatype "A" [MV "p"]) (MV "p") (Datatype "A" [MV "p"])))


