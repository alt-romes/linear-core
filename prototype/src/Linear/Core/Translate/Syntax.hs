{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE MonoLocalBinds, DataKinds #-}
{-# LANGUAGE DeriveTraversable, TemplateHaskell #-}
module Linear.Core.Translate.Syntax
  ( module Linear.Core.Translate.Syntax

  -- * Re-exports
  , pretty
  )
  where

import GHC.Utils.Outputable (showPprUnsafe, ppr)
import GHC.Types.Literal
-- import Data.Kind
-- import GHC.TypeLits
import Debug.Trace
import Data.Text (Text)
import qualified Data.Text as T
import Data.Functor.Foldable.TH (makeBaseFunctor)
import qualified Data.Char as C
import Data.Map (Map)
import Data.Set (Set)
import qualified Data.Map as M
-- import qualified Data.Set as S

import Data.Functor.Foldable
import Prettyprinter

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

--------------------------------------------------------------------------------
----- Var Things ---------------------------------------------------------------
--------------------------------------------------------------------------------

data Id = MkId { varType   :: Ty
               , idBinding :: IdBinding
               , varName'   :: Name
               }
               deriving Show
newtype MultVar = MkMultVar { varName' :: Name }
  deriving (Eq,Show)

varName :: Var -> Name
varName (Id _ _ n)  = n
varName (MultVar n) = n

data Var = Id' Id | MultVar' MultVar deriving Show
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

--------------------------------------------------------------------------------
----- Syntax -------------------------------------------------------------------
--------------------------------------------------------------------------------

-- | A UsageEnv (Δ) is a set of variables that need to be used linearly
type UsageEnv = Set Name

data IdBinding = LambdaBound Mult
               | DeltaBound UsageEnv -- ^ Let and case bound variables. Case variables do have many usage environments, but in practice (when they occur in a context), they have just one usage environment
               deriving (Eq, Show)

data BindingSite = LambdaBindSite | LetBindSite deriving (Eq, Show)

-- I suppose we need TyMultVar to type mult applications, despite no term with
-- that type existing.
data Ty
  -- = TyMultVar Name          -- p -- no, multiplicities can't exist on their own, only attached to functions (or datatype univ. vars)
  = Datatype Name [Mult]    -- K π_1 ... π_n
  | FunTy   Ty   Mult Ty    -- φ ->π σ
  | Scheme  Name Ty         -- ∀p. φ
  deriving (Show)

data Expr b where
  Var  :: b -> Expr b -- Only term variables and constructors. Type variables at the term level would be (Ty (TyMultVar "p"))
  Lit  :: Literal_ -> Expr b
  Lam  :: b -> Expr b -> Expr b
  App  :: Expr b -> Expr b -> Expr b
  Let  :: Bind b -> Expr b -> Expr b
  Case :: Expr b -> b -> [Alt b] -> Expr b
  Mult :: Mult -> Expr b

  -- For bidirectional type-checking the Core language.
  -- After type-checking we have Expr Id, and this
  -- construct doesn't occur in the elaborated program.
  Ann  :: Expr b -> Ty -> Expr b

deriving instance Show b => Show (Expr b)

data Bind b = NonRec b (Expr b)
            | Rec [(b, Expr b)]
            deriving (Show)

data Alt b
    = Alt (AltCon b) [b] (Expr b)
    deriving (Show)

data AltCon b
  = DataAlt (DataCon b)
  --  ^ A plain data constructor: @case e of { Foo x -> ... }@.

  | DEFAULT
  -- ^ Trivial alternative: @case e of { _ -> ... }@

deriving instance Show b => Show (AltCon b)

newtype Literal_ = L Literal deriving Eq
instance Show Literal_ where
  show (L l) = showPprUnsafe l

-- | All constructors are of the form K~\overline{x{:}_\pi\sigma}
-- We record the information about the multiplicity and type of each argument
-- to the constructor. No existentials, but a datatype may be parametrized by
-- mult. variables.
data DataCon b where
  DataCon :: Name        -- ^ dcName
          -> [Mult]      -- ^ dcUnivMultVars
          -> [Scaled Ty] -- ^ dcArgTys, with corresponding multiplicity
          -> DataCon Var -- ^ Elaborated DataCon
  DataConName :: Name -> DataCon Name -- ^ Parsed DataCon
  
deriving instance Show b => Show (DataCon b)

data Scaled a = Scaled !Mult a
  deriving (Eq,Show)

type Ctx = Map Name Var
-- ^ The context maps names to variables that can be
-- * Lambda bound vars (x :_π σ)
-- * Let bound vars    (x :_Δ σ)
-- * Case bound vars   (x :_\ov{Δ} σ)
-- * Mult vars         (@π)
-- * DataCons          (K:σ), which are really just a special sort of top-level closed-Δ let-bound vars (K :_\ov{\cdot} σ)

-- | Γ |- e : τ
data Term b = Term Ctx (Expr b) Ty
  deriving Show

-- Recursion schemes
makeBaseFunctor ''Expr
makeBaseFunctor ''Ty

type CoreTerm = Term Var
type CoreAlt  = Alt Var
type CoreBind = Bind Var
type CoreExpr = Expr Var

erase :: CoreTerm -> CoreExpr
erase (Term _ e _) = e

varUE :: Var -> Maybe UsageEnv
varUE (Id _ (DeltaBound ue) _) = Just ue
varUE _ = Nothing

-- | Sets the UE of a delta-bound var to the given usage environment.
-- Ignores the given UE otherwise
setUE :: Var -> UsageEnv -> Var
setUE (Id t (DeltaBound _ue_old) n) ue = Id t (DeltaBound ue) n
setUE x _ = trace "Setting the UE of a non DeltaBound var" x

-- | Sets the IdBinding of an Id to the given variable, and does nothing to
-- multiplicity variables
setIdBinding :: Var -> IdBinding -> Var
setIdBinding (Id t _ n) b = Id t b n
setIdBinding x _ = x

varId :: Var -> Id
varId (Id' i) = i
varId _ = error "varId: Not an Id"


--------------------------------------------------------------------------------
----- Pretty-printing ----------------------------------------------------------
--------------------------------------------------------------------------------

instance Pretty Var where
  pretty (Id ty _ n) = parens $ pretty n <+> "::" <+> pretty ty
  pretty (MultVar n) = pretty n

instance Pretty Mult where
  pretty One = "1"
  pretty Many = "ω"
  pretty (MV m) = pretty m

instance Pretty b => Pretty (Bind b) where
  pretty (NonRec b e) = pretty b <+> "=" <+> pretty e
  pretty (Rec ls) = vsep $ map (\(b,e) -> pretty b <+> "=" <+> pretty e) ls

instance Pretty (DataCon b) where
  pretty (DataCon name _ _) = pretty name
  pretty (DataConName name) = pretty name

instance Pretty b => Pretty (AltCon b) where
  pretty DEFAULT = "_"
  pretty (DataAlt dc) = pretty dc

instance Pretty b => Pretty (Alt b) where
  pretty (Alt k [] e) = pretty k <+> "->" <+> pretty e <> ";" -- the last Alt will also have a ; but fine
  pretty (Alt k bnds e) = pretty k <+> hsep (map pretty bnds) <+> "->" <+> pretty e <> ";" -- the last Alt will also have a ; but fine

instance Pretty b => Pretty (Expr b) where
  pretty = para go where
    go = \case
      VarF var -> pretty var
      LamF b (_,e) -> "λ" <> pretty b <+> "->" <+> e

      -- Applications
      AppF (Var _, e1) (Var _, e2)  -> e1 <+> e2
      AppF (Var _,e1)  (Mult _, e2) -> e1 <+> e2
      AppF (Var _,e1)  (_, e2)      -> e1 <+> parens e2
      AppF (App _ _, e1) (Var _, e2)  -> e1 <+> e2
      AppF (App _ _,e1)  (Mult _, e2) -> e1 <+> e2
      AppF (App _ _,e1)  (_, e2)      -> e1 <+> parens e2
      AppF (_,e1) (Var _, e2)       -> parens e1 <+> e2
      AppF (_,e1) (Mult _, e2)      -> parens e1 <+> e2
      AppF (_,e1) (_, e2)           -> parens e1 <+> parens e2

      LetF bnd (_,e) -> "let" <+> align (pretty bnd) <+> "in" <+> e
      CaseF (_,scrt) bnd alts -> "case" <+> scrt <+> "of" <+> pretty bnd <+> braces ("" <+> align (vsep (map pretty alts)) <+> "")
      MultF m -> "@" <> pretty m -- can it only occur in argument position?

      LitF (L l) -> pretty $ showPprUnsafe (ppr l)

      AnnF (Lam _ _,e) t -> parens e <+> "::" <+> pretty t
      AnnF (_,e) t -> e <+> "::" <+> pretty t

instance Pretty Ty where
  pretty = cata go where
    go (DatatypeF name [])   = pretty name
    go (DatatypeF name mult) = pretty name <+> hsep (map pretty mult)
    go (FunTyF t1 One t2)    = parens t1 <+> "-o" <+> parens t2
    go (FunTyF t1 Many t2)   = parens t1 <+> "->" <+> parens t2
    go (FunTyF t1 m t2)      = parens t1 <+> "%" <> pretty m <+> "->" <+> parens t2
    go (SchemeF n ty)        = "∀" <> pretty n <> "." <+> ty


--------------------------------------------------------------------------------
----- Renaming Substitution ----------------------------------------------------
--------------------------------------------------------------------------------

-- | Name substitution, for renaming
-- We use these substitutions for equality in the Eq instance of Ty
type RenameEnv = M.Map Name Name

class Renamable a where
  rename :: RenameEnv -> a -> a

instance Renamable Name where
  rename env n = case M.lookup n env of
                   Nothing -> n
                   Just n' -> n'

instance Renamable a => Renamable [a] where
  rename env = map (rename env)

deriving newtype instance Renamable MultVar

instance Renamable Mult where
  rename env = \case
    Many -> Many
    One  -> One
    MV' mv -> MV' $ rename env mv

instance Renamable Ty where
  rename env = \case
      Datatype name mults -> Datatype name (rename env mults)
      FunTy t1 m t2       -> FunTy (rename env t1) (rename env m) (rename env t2)
      Scheme n ty
        | Nothing <- M.lookup n env
        -- if it's not binding the same name, rename
        -> Scheme n (rename env ty)
        | otherwise --, don't rename this name in its body
        -> Scheme n (rename (M.delete n env) ty)

--------------------------------------------------------------------------------
----- Some Equality ------------------------------------------------------------
--------------------------------------------------------------------------------

instance Eq Ty where
  Datatype name mults == Datatype name' mults'
    | C.isLower (T.head name) || C.isLower (T.head name')
    -- One of the variables used to be a type variable that can be instantiated to any type.
    -- This is one of the awfulawful hacks we have to do because we translate
    -- Core to a simpler representation without type abstractions
    -- We assume unification is OK, and move on
    = mults == mults'

    -- Another great hack, if we keep coming up with these this will be
    -- absolutely horrendous, and we'll have to try again typechecking core
    -- directly
    --
    -- When we look through a pattern synonym whose RHS is an implicit
    -- parameter (like ?callstack :: CallStack), we get "IP" as the data type,
    -- which is the TyCon of an ImplicitParameter class, it seems)
    -- We just unify it against anything. Hack.
    | name == "IP" || name' == "IP"
    = mults == mults'

    -- Do a normal thing
    | otherwise
    = name == name' && mults == mults'
  FunTy t1 m t2 == FunTy t1' m' t2' = t1 == t1' && m == m' && t2 == t2'
  Scheme n ty == Scheme n' ty' = ty == rename (M.singleton n' n) ty'
  _ == _ = False

-- These have to be defined later here because of template haskell and the Eq Ty needing the `rename` function

deriving instance Eq Id
deriving instance Eq Var

deriving instance Eq b => Eq (Expr b)
deriving instance Eq b => Eq (AltCon b)
deriving instance Eq b => Eq (DataCon b)
deriving instance Eq b => Eq (Bind b)
deriving instance Eq b => Eq (Alt b)

