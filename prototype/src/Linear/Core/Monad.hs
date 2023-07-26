{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE OverloadedStrings #-}
-- | A monad transformer for computations that consume and thread through resources from a linear
-- environment
module Linear.Core.Monad
  ( LinearCtxT
  , use
  , extend
  , unrestricted
  )
  where

import Control.Monad
import Data.String
import Control.Monad.State
import Control.Monad.Except
import Data.Map  as M
import Data.List as L
import Data.Maybe

-- | Computations that thread through a linear context from which resources
-- must be used exactly once.
-- (i.e. models computations that are well-defined under a linear context)
newtype LinearCtxT k v m a = LinearCtxT { unLC :: StateT (M.Map k v) m a }
  deriving (Functor, Applicative, Monad, MonadTrans)


-- | Uses a resource from the linear environment, making it unavailable in subsequent computations.
-- If the key doesn't exist, no resources are consumed
use :: (Ord k, Monad m) => k -> LinearCtxT k v m (Maybe v)
use key = LinearCtxT do
  mv <- gets (M.lookup key)
  case mv of
    Nothing -> return Nothing
    Just v -> do
      modify (M.delete key)
      return (Just v)
  

-- | Extend a computation that threads linear resources with a resource that
-- must definitely not escape its scope (i.e. the given computation must
-- consume the resource it was extended with).
--
-- If the resource escapes the given computation, the resulting computation fails.
--
-- If the resource was already in the context it also fails.
extend :: (Ord k, MonadError e m, IsString e, Show k)
       => k -> v -> LinearCtxT k v m a -> LinearCtxT k v m a
extend key value computation = LinearCtxT do
  gets (isNothing . M.lookup key) >>= \case
    False -> throwError $ fromString $ "Tried to extend a computation with a resource that was already in the environment: " ++ show key ++ "."
    True -> do
      modify (M.insert key value)
      result <- unLC computation
      wasConsumed key >>= \case
        True -> return result
        False -> throwError $ fromString $
          "The linear resource " ++ show key ++ " wasn't consumed in the computation extended with it"
        where
          wasConsumed x = gets $ isNothing . M.lookup x


-- | Runs a computation that threads linear resources and fails if the
-- computation consumed any resource at all (i.e. fails if the input and output
-- resources are not the same).
--
-- That is, run a computation that does not use linear resources (i.e. an unrestricted computation)
unrestricted :: (Eq k, MonadError e m, IsString e, Show k) => LinearCtxT k v m a -> LinearCtxT k v m a
unrestricted computation = LinearCtxT do
  prev <- gets M.keys
  result <- unLC computation
  after <- gets M.keys
  when (prev /= after) $
    throwError $ fromString $
      "An unrestricted computation should consume no linear resources, but instead it used " ++ show (prev L.\\ after) ++ "."
  return result



