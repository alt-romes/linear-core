{-# LANGUAGE LinearTypes #-}


f :: a %1 -> a
f x = let y = x in y

main = pure ()

