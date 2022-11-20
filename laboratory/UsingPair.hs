{-# LANGUAGE LinearTypes #-}

p :: (Int, Int) %1 -> (Int, Int)
p x = case x of
        w@(y,z) -> w

main = pure ()
