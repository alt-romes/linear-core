{-# LANGUAGE LinearTypes, UnicodeSyntax, BlockArguments #-}
module Main where


{- Examples from the thesis -}

{- Lets -}

f1 :: (a ⊸ b) -> a ⊸ b
f1 use x = let y = use x in y

{- Recursive lets -}

{- Cases -}


-- ROMES:TODO: I have to invoke the linear core plugin directly with the
-- examples, since otherwise compiling Haskell with type errors is not
-- possible, and `-fdefer-type-errors` makes the program useless, only having
-- runtime type errors...
main :: IO ()
main = putStrLn "Hello, Haskell!"
