{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE RebindableSyntax #-}
module Main where

import GHC.Exts (Multiplicity(..))

import Prelude.Linear
import qualified System.IO.Linear as Linear
import System.IO
import Control.Functor.Linear as Linear

-- f1 :: a %1 -> (a, a)
-- f1 x = (x,x)



f2 :: a %Many -> (a, a)
f2 x = (x,x)

