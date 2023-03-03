module X where

--TODO: Add to presentation
--- Haskell
null :: [a] -> Bool
null [] = True
null _  = False

--- Core
-- null :: ∀ a. [a] -> Bool
-- null = \ @a (x :: a) ->
--   case x of
--     [] -> True
--     (:) y ys -> False
