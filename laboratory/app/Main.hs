{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE RebindableSyntax #-}
module Main where

import qualified Prelude
import GHC.Exts (Multiplicity(..))

import Prelude.Linear
import Data.Unrestricted.Linear
import qualified System.IO.Linear as Linear
import System.IO
import Control.Functor.Linear as Linear
import Prelude.Linear
import qualified Control.Functor.Linear as Control
import qualified System.IO.Resource.Linear as Linear
import qualified Data.Text as Text
import qualified Prelude

import Files

-- f1 :: a %1 -> (a, a)
-- f1 x = (x,x)


f2 :: a %Many -> (a, a)
f2 x = (x,x)

main :: IO ()
main = Files.linearWriteToFile

linearWriteToFile :: IO ()
linearWriteToFile = Linear.run $ Control.do
  handle1 <- Linear.openFile "test.txt" Linear.WriteMode
  handle2 <- Linear.hPutStrLn handle1 (Text.pack "hello there")
  () <- Linear.hClose handle2
  Control.return (Ur ())
