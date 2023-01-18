{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GHC2021 #-}

import Data.Kind
import Prelude hiding (head)

data Nat = Z | S Nat

data Vec (n :: Nat) (a :: Type) where
  Nil :: Vec Z a
  Cons :: a -> Vec m a -> Vec (S m) a

head :: Vec (S n) a -> a
head (Cons x _) = x
head Nil = undefined

main = do
  pure $ head $ Cons '1' Nil
  -- pure $ head $ Nil
  pure ()
