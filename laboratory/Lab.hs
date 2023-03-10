{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE UnicodeSyntax #-}
module Lab where


f :: (∀ p. Int %p -> Int) -> (∀ p. Int %p -> Int)
f = id

g x = case x of z {
        z@Atom    -> ..z.
        z@C a b c -> ...z
        z@D d e   -> ...z
                  }

main :: IO ()
main = pure ()

