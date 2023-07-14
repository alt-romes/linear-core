module Linear.Core.Parser where

import Data.Text (Text)
-- import qualified Data.Text as T

import Data.Functor.Identity
import Data.Void

import Text.Megaparsec

type Parser = ParsecT Void Text Identity

Control

