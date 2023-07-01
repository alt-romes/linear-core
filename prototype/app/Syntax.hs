{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable,
   DeriveTraversable, TemplateHaskell, TypeFamilies #-}
module Syntax where

import Data.Functor.Foldable.TH (makeBaseFunctor)
import Data.Map (Map)
import qualified Data.Map as M
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

* We must also implement the algorithm for inferring usage environments, which
we still need to figure out when exactly it should be run
-}

type Name = String

data Id = MkId { varType   :: Ty
               , idBinding :: IdBinding
               , varName'   :: Name
               }
               deriving (Eq, Show)
newtype MultVar = MkMultVar { varName' :: Name }
  deriving (Eq,Show)

varName :: Var -> Name
varName (Id _ _ n)  = n
varName (MultVar n) = n

data Var = Id' Id
         | MultVar' MultVar
         deriving (Eq, Show)
{-# COMPLETE Id, MultVar #-}

pattern Id :: Ty -> IdBinding -> Name -> Var
pattern Id ty binding name = Id' (MkId ty binding name)

pattern MultVar :: Name -> Var
pattern MultVar name = MultVar' (MkMultVar name)

data Mult = Many       -- ω
          | One        -- 1
          | MV' MultVar -- π
          deriving (Eq,Show)
{-# COMPLETE Many,One,MV #-}

pattern MV :: Name -> Mult
pattern MV name = MV' (MkMultVar name)

type UsageEnv = Map Name Mult

data IdBinding = LambdaBound Mult
               | DeltaBound UsageEnv -- ^ Let and case bound variables. Case variables do have many usage environments, but in practice (when they occur in a context), they have just one usage environment
               deriving (Eq, Show)

data Ty
  -- = TyMultVar Name
  = Datatype Name [Mult]    -- K π_1 ... π_n
  | FunTy   Ty   Mult Ty    -- φ ->π σ
  | Scheme  Name Ty         -- ∀p. φ
  deriving (Eq,Show)

data Expr b
  = Var b -- Only term variables, type variables at the term level would be (Ty (TyMultVar "p"))
  | Lam b (Expr b)
  | App (Expr b) (Expr b)
  | Let (Bind b) (Expr b)
  | Case (Expr b) b [Alt b]
  | Mult Mult
  deriving (Eq,Show)

data Bind b = NonRec b (Expr b)
            | Rec [(b, Expr b)]
            deriving (Eq,Show)

data Alt b
    = Alt AltCon [b] (Expr b)
    deriving (Eq,Show)

data AltCon
  = DataAlt DataCon   --  ^ A plain data constructor: @case e of { Foo x -> ... }@.
                      -- Invariant: the 'DataCon' is always from a @data@ type, and never from a @newtype@

  | DEFAULT           -- ^ Trivial alternative: @case e of { _ -> ... }@
  deriving (Eq,Show)

-- | All constructors are of the form K~\overline{x{:}_\pi\sigma}
-- We record the information about the multiplicity and type of each argument
-- to the constructor. No existentials, but a datatype may be parametrized by
-- mult. variables.
data DataCon
  = DataCon { dcName :: Name
            , dcUnivMultVars :: [Mult]
            , dcArgTys :: [Scaled Ty]
            }
            deriving (Eq,Show)

data Scaled a = Scaled !Mult a
  deriving (Eq,Show)

type Ctx = Map Name Var
-- ^ The context maps names to variables that can be
-- * Lambda bound vars (x :_π σ)
-- * Let bound vars    (x :_Δ σ)
-- * Case bound vars   (x :_\ov{Δ} σ)
-- * Mult vars         (π)
-- * DataCons          (K:σ), which are really just a special sort of top-level closed-Δ let-bound vars (K :_\ov{\cdot} σ)

-- | Γ |- e : τ
data Term b = Term Ctx (Expr b) Ty
  deriving Show

-- Recursion schemes
makeBaseFunctor ''Expr
makeBaseFunctor ''Ty

type CoreTerm = Term Var
type CoreAlt  = Alt Var
type CoreBndr = Bind Var
type CoreExpr = Expr Var

erase :: CoreTerm -> CoreExpr
erase (Term _ e _) = e

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
