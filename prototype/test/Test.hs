{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fplugin=Linear.Core.Plugin #-}

-- |
---------- Tests ---------------------------------------------------------------
-- Our tests consist solely of typechecking this module using the plugin.
-- Annotate functions that are not expected to typecheck by prefixing them with @fail_@
module Main where


import GHC.Plugins
import Linear.Core.Plugin



main :: IO ()
main = pure ()

