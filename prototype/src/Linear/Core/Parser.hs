{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE BlockArguments #-}
{-# OPTIONS -Wno-orphans #-} -- HasHints Void
module Linear.Core.Parser where

{-
It could be more interesting to also transform Core into this language, than to
just parse it standalone.
-}

import System.IO
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as T

import Data.Functor.Identity
import Data.Void

import Control.Monad.Except

import Text.Megaparsec
import Text.Megaparsec.Char
import Control.Monad.Combinators.Expr
import qualified Text.Megaparsec.Char.Lexer as L

import Linear.Core.Syntax
import Error.Diagnose
import Error.Diagnose.Compat.Megaparsec
import System.Exit

type Parser = ParsecT Void Text Identity

--------------------------------------------------------------------------------
----- Low-level parsing/lexing -------------------------------------------------
--------------------------------------------------------------------------------

-- space consumer
sc :: Parser ()
sc = L.space
  space1
  (L.skipLineComment "--")
  empty

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: Text -> Parser Text
symbol = L.symbol sc

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

keyword :: Text -> Parser Text
keyword kwd = lexeme (string kwd <* notFollowedBy alphaNumChar)

reservedWords :: [Text]
reservedWords = ["case", "let", "rec", "of", "in"]

-- | Starts with upper case
dataIdentifier :: Parser Text
dataIdentifier = (lexeme . try) (T.pack <$> ((:) <$> upperChar <*> many alphaNumChar)) <?> "data identifier"

identifier :: Parser Text
identifier = (lexeme . try) (p >>= check) <?> "identifier"
  where
    p       = T.pack <$> ((:) <$> letterChar <*> many alphaNumChar)
    check x = if x `elem` reservedWords
                then fail $ T.unpack $ "keyword \"" <> x <> "\" cannot be an identifier"
                else return x


--------------------------------------------------------------------------------
----- Parsing ------------------------------------------------------------------
--------------------------------------------------------------------------------

typeP :: Parser Ty
typeP = makeExprParser typeTermP table <?> "type" where
  table = [ [ InfixR (flip FunTy <$> (symbol "%" *> multP <* symbol "->"))
            , InfixR ((`FunTy` One) <$ symbol "-o")
            , InfixR ((`FunTy` Many) <$ symbol "->")
            ]
          ]
  typeTermP = choice
    [ datatypeP
    , schemeP
    ]
  datatypeP = Datatype <$> dataIdentifier <*> many multP
  schemeP   = Scheme <$> ((symbol "∀" <|> symbol "forall") *> identifier) <*> (symbol "." *> typeP)

exprP :: Parser (Expr Name)
exprP = withAnnP (makeExprParser termP table <?> "expression") where
      table = [ [InfixL (App <$ symbol "")]
              ]

-- | Tries to parse a type annotation after on this expression
withAnnP :: Parser (Expr Name) -> Parser (Expr Name)
withAnnP expr = do
  e <- expr
  (Ann e <$> (symbol "::" *> typeP)) <|> return e


termP :: Parser (Expr Name)
termP = choice
    [ parens exprP
    , caseP
    , letrecP
    , letP
    , lamP
    , multExprP
    , atomP
    ] <?> "term"

caseP :: Parser (Expr Name)
caseP = (do
  scrut <- keyword "case" *> exprP <* keyword "of"
  casebinder <- identifier
  alternatives <- symbol "{" *> many altP <* symbol "}"
  return (Case scrut casebinder alternatives)) <?> "case"

altP :: Parser (Alt Name)
altP = (do
  con <- altconP
  vars <- many identifier
  body <- symbol "->" *> exprP <* (symbol ";" <|> lookAhead (symbol "}"))
  return (Alt con vars body)) <?> "alternative"

altconP :: Parser (AltCon Name)
altconP = choice
  [ DEFAULT               <$ symbol "_"
  , DataAlt . DataConName <$> dataIdentifier
  ]

letrecP :: Parser (Expr Name)
letrecP = (do
  -- no type annotations for now!
  -- i think we'll need bidirectional typing during inference to ensure we get
  -- the linearity annotations right (or at least some unification with the annotations).
  _      <- try (keyword "let" *> keyword "rec")
  binders <- many ((,) <$> identifier <*> (symbol "=" *> exprP <* eol))
  let_body    <-  keyword "in" *> exprP
  return (Let (Rec binders) let_body)) <?> "let rec"

letP :: Parser (Expr Name)
letP = (do
  binder      <- keyword "let" *> identifier 
  binder_body <-       symbol "=" *> exprP
  let_body    <-  keyword "in" *> exprP
  return (Let (NonRec binder binder_body) let_body)) <?> "let"

lamP :: Parser (Expr Name)
lamP = Lam <$> ((symbol "\\" <|> symbol "λ") *> identifier <* symbol "->") <*> exprP <?> "lambda"

multExprP :: Parser (Expr Name)
multExprP = Mult <$> (symbol "@" *> multP) <?> "mult expr"

multP :: Parser Mult
multP = choice
  [ One  <$ symbol "1"
  , Many <$ symbol "ω"
  , MV   <$> identifier
  ] <?> "mult"

atomP :: Parser (Expr Name)
atomP = Var <$> identifier <?> "atom"

moduleP :: Parser (Module Name)
moduleP = Module <$> many exprP <?> "module"

--------------------------------------------------------------------------------
----- Entry points to the parser -----------------------------------------------
--------------------------------------------------------------------------------

parseExpr :: MonadError (Diagnostic Text) m
          => Text -> m (Expr Name)
parseExpr str
  = case parse exprP "<parseExpr>" str of
      Left e -> throwError (errorDiagnosticFromBundle Nothing "Parse error on input" Nothing e)
      Right e -> return e

parseModule :: MonadIO m
            => FilePath
            -> m (Module Name)
parseModule path = do
  cts <- liftIO $ T.readFile path
  case parse moduleP path cts of
    Left e -> do
      let diag  = errorDiagnosticFromBundle Nothing ("Parse error on input" :: String) Nothing e
          -- diag' = addFile
      printDiagnostic stderr True False 4 defaultStyle diag
      liftIO $ exitWith (ExitFailure 1)
    Right m -> return m

instance HasHints Void msg where
  hints _ = mempty
