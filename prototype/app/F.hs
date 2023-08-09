{-# LANGUAGE LinearTypes, UnicodeSyntax #-}
module F where

data Y = Y Y Y

f y = let z = Y z y in z

r,t :: Bool -> Bool
r x = case x of
        True -> t x
        False -> True
t x = case x of
        True -> False
        False -> r x

my_f :: Int -> Int
my_f x = x

my_f1 :: Int %1 -> Int
my_f1 x = x

s :: (a -> Maybe b) %1 -> (a -> Maybe b)
s = undefined


my_t :: Maybe Int -> Maybe Int
my_t x = x

my_g :: (a %1 -> b) -> Maybe a %1 -> Maybe b
my_g f x = case x of
             Nothing -> Nothing
             Just y -> Just (f y)

