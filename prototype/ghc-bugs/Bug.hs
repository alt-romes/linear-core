{-# LANGUAGE LinearTypes #-}
module Bug where

-- f :: a -> b
-- f x = x

f1 :: (a %1 -> b) -> a %1 -> b
f1 use x = let y = use x in y


