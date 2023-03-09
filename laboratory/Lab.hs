{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE UnicodeSyntax #-}
module Lab where


f :: (∀ p. Int %p -> Int) -> (∀ p. Int %p -> Int)
f = id

g x = case x of z {
        Atom    -> ...
        C a b c -> ...
        D z x   -> ...
                  }

main :: IO ()
main = pure ()

