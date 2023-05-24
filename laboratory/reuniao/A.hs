{-# LANGUAGE LinearTypes, UnicodeSyntax, MagicHash #-}
module A where

import B qualified as Unsafe
import GHC.Exts

data Alg a = K1 a
           | K2 a a
           | K3

f :: FUN 'One Int (IO ())
f x = case x of
        -- I# y -> case consumeInt y of
        --           () -> pure ()
        _ -> case consumeInt' x of
               () -> pure ()

-- Não é igual aos outros?
h :: FUN 'One Int Int
h x = case x of
        _ -> x
-- VS
g :: FUN 'One Int Int
g x = case x of
        y -> y
-- VS
-- u :: FUN 'One Int Int
-- u x = case x of z
--         _ -> z

v :: Alg Int ⊸ Alg Int
v x = case x of
        y -> y

kk :: Alg Int ⊸ Alg Int
kk x = case v x of
         y -> y

-- Usage env do case binder acaba por ser o contexto linear de <expr>
-- Duplicado de forma parecida ao resto das coisas...

consumeInt :: Int# ⊸ ()
consumeInt = Unsafe.toLinear (\x -> ())
consumeInt' :: Int ⊸ ()
consumeInt' = Unsafe.toLinear (\x -> ())


