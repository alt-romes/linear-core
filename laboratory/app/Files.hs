{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE QualifiedDo #-}
module Files where

import Prelude.Linear
import qualified Control.Functor.Linear as Control
import qualified System.IO.Resource.Linear as Linear
import qualified Data.Text as Text
import qualified Prelude

-- class Functor f where
--   fmap :: (a %1 -> b) -> f a %1 -> f b

-- class Functor f => Applicative f where
--   (<*>) :: f (a %1 -> b) %1 -> f a %1 -> f b
--   pure :: a -> f a

-- class Applicative m => Monad m where
--   (>>=) :: m a %1 -> (a %1 -> m b) %1 -> m b

linearWriteToFile :: IO ()
linearWriteToFile = Linear.run $ Control.do
  handle1 <- Linear.openFile "test.txt" Linear.WriteMode
  handle2 <- Linear.hPutStrLn handle1 (Text.pack "hello there")
  () <- Linear.hClose handle2
  Control.return (Ur ())
