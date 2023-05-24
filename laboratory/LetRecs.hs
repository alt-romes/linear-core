
module LetRecs where

f y =
  let g x = case x of
                True -> h x
                False -> True
      h x = case x of
              True -> False
              False -> g x
      l x = z x
      {-# NOINLINE g #-}
      {-# NOINLINE h #-}
      {-# NOINLINE l #-}
    in g y || l y


z :: Bool -> Bool
z = undefined
{-# NOINLINE z #-}
