{-# LANGUAGE LinearTypes #-}
module A
where

f :: (a %1 -> a) -> a %1 -> a
f use x = let y = use x in y

