{-# LANGUAGE LinearTypes, EmptyCase #-}
module M where

{-# NOINLINE f #-}
f :: a %1-> ()
f x = case () of {}

