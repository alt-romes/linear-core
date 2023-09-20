{-# LANGUAGE LinearTypes, UnicodeSyntax, BlockArguments, OverloadedStrings #-}
module Main where
import GHC.Core.Opt.Monad
import GHC.Driver.Main (initHscEnv)
import GHC.Plugins
import Linear.Core
import Data.String

{- Examples from the thesis -}

{- Lets -}

-- f1 :: (a ⊸ b) -> a ⊸ b
-- f1 use x = let y = use x in y

{- Recursive lets -}

{- Cases -}


-- ROMES:TODO: I have to invoke the linear core plugin directly with the
-- examples, since otherwise compiling Haskell with type errors is not
-- possible, and `-fdefer-type-errors` makes the program useless, only having
-- runtime type errors...
main :: IO ()
main = do
  putStrLn "Hello, Haskell!"

  hscEnv <- initHscEnv Nothing
  let
    modu
      = mkModule (stringToUnit "linear-core-tests-unit") (mkModuleName "Linear.Core.Tests")
                 

  print . map showPprUnsafe . fst =<<
    runCoreM hscEnv
             mempty
             's'
             modu
             neverQualify -- or alwaysQualify
             noSrcSpan
             mainLinearCoreTest

mainLinearCoreTest :: CoreM [SDoc]
mainLinearCoreTest
  = runLinearCore
    [ f1
    -- , f2
    ]

f1 :: CoreBind
f1 = NonRec 


mkId :: String -> Mult -> Type -> Id
mkId s = mkLocalId (mkInternalName (mkVarOcc s) noSrcSpan)

