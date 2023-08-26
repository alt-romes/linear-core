{-# LANGUAGE LinearTypes #-}
module A
where

import Data.Function

-- f :: (a %1 -> a) -> a %1 -> a
-- f use x = let y = use x in y


f6 :: Bool -> a -> a
f6 bool =
  let go b = case b of
        True -> x
        False -> go (not b)
   in go bool

f6' :: forall a. Bool -> a -> a
f6' bool x = (fix go') bool
  where
    go' :: (Bool -> a) -> (Bool -> a)
    go' rec b = case b of
            True -> x
            False -> rec (not b)

