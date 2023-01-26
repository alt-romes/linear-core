{-# LANGUAGE LinearTypes #-}

f :: (Bool %1 -> Int) -> Int
f c = c True

g :: (Bool -> Int) -> Int
g c = c False

h :: (Bool %m -> Int)
h False = 0
h True = 1

t :: Bool %m -> (Bool, Bool)
t x = (x, x)

main = do
  print $ f h
  print $ g h
  pure ()

