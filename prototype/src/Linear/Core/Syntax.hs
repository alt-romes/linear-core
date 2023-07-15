{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeFamilies, DataKinds #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable,
   DeriveTraversable, TemplateHaskell, TypeFamilies #-}
module Linear.Core.Syntax where

import Data.Kind
import GHC.TypeLits
import Debug.Trace
import Data.Text (Text)
import qualified Data.Text as T
import Data.Functor.Foldable.TH (makeBaseFunctor)
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S

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

type Name = Text

newtype Module b = Module [Expr b]

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

-- | A UsageEnv (Δ) is a set of variables that need to be used linearly
type UsageEnv = Set Name

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
  = Var b -- Only term variables and constructors. Type variables at the term level would be (Ty (TyMultVar "p"))
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
    = Alt (AltCon b) [b] (Expr b)
    deriving (Eq,Show)

data AltCon b
  = DataAlt (DataCon b)
  --  ^ A plain data constructor: @case e of { Foo x -> ... }@.

  | DEFAULT
  -- ^ Trivial alternative: @case e of { _ -> ... }@

deriving instance Eq b => Eq (AltCon b)
deriving instance Show b => Show (AltCon b)


-- | All constructors are of the form K~\overline{x{:}_\pi\sigma}
-- We record the information about the multiplicity and type of each argument
-- to the constructor. No existentials, but a datatype may be parametrized by
-- mult. variables.
data DataCon b where
  DataCon :: Name        -- ^ dcName
          -> [Mult]      -- ^ dcUnivMultVars
          -> [Scaled Ty] -- ^ dcArgTys, with corresponding multiplicity
          -> DataCon Id  -- ^ Elaborated DataCon
  DataConName :: Name -> DataCon Name -- ^ Parsed DataCon
  
deriving instance Eq b => Eq (DataCon b)
deriving instance Show b => Show (DataCon b)

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

varUE :: Var -> Maybe UsageEnv
varUE (Id _ (DeltaBound ue) _) = Just ue
varUE _ = Nothing

setUE :: Var -> UsageEnv -> Var
setUE (Id t (DeltaBound _ue_old) n) ue = Id t (DeltaBound ue) n
setUE x _ = trace "Setting the UE of a non DeltaBound var" x

varId :: Var -> Id
varId (Id' i) = i
varId _ = error "varId: Not an Id"

