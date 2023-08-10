{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE OverloadedStrings #-}
-- | A monad transformer for computations that consume and thread through resources from a linear
-- environment
module Linear.Core.Monad
  ( LinearCoreT
  , runLinearCoreT
  -- * Operations
  , use
  , extend
  , unrestricted
  , record
  , recordNonLinear
  )
  where

import qualified GHC.Types.Unique.FM as FM
import Control.Monad
import Data.String
import Control.Monad.State
import Control.Monad.RWS.CPS
import Control.Monad.Except
import GHC.Types.Var
import GHC.Types.Var.Env

import Linear.Core.Multiplicities
import GHC.Driver.Ppr (showPprUnsafe)
import qualified Data.Map as M

-- | Computations that thread through a linear context from which resources must
-- be used exactly once, and resources of other multiplicities that can be
-- consumed unrestrictedly
-- (i.e. models computations that are well-defined under a mixed multiplicity context)
--
-- See 'use' for what using a variable means in these computations
--
-- LinearCoreT
-- * The State, (VarEnv Mult), represents the variables in scope. The variables
-- in scope can be linear or non-linear.
--   * When we use a variable that is in scope (see 'use'), we remove it from the
--   list of variables in scope if it was a linear variable
--   * In practice, the state allows threading of resources as per the
--   input/output resource management strategy to typecheck linear types
-- * The Writer, [Var], records all the variables that were used in a
-- computation, including the unrestricted variables.
--   * One can trivially determine the linear variables used in a computation by
--   taking the \setminus between the state before the computation and the state
--   after the computation, because linear resources disappear from the context
--   when used
--   * However, we need a way to record the unrestricted and Δ variables that were
--   used in a computation in order to compute the recursive usage environments
--   for a group of recursive let bindings.
--   * That's why we have [Var] in writer, it records all the unrestricted or Δ used variables in
--   a computation (we are careful to reset it after recording, to be sure
--   they don't leak from one computation to the other)
-- * The Reader, Bool, determines whether to record all variables used in the writer env.
--    * This bool will only be true when recordNonLinear sets in order to record variables.
--    * This ensures we only collect variables within recordNonLinear, after which we wipe the writer
newtype LinearCoreT m a = LinearCoreT { unLC :: RWST Bool [Var] (M.Map Var IdBinding) m a }
  deriving (Functor, Applicative, Monad, MonadTrans)

runLinearCoreT :: (MonadError e m, IsString e) => M.Map Var IdBinding -> LinearCoreT m a -> m a
runLinearCoreT s comp = do
  (a, renv, _unrestrictedUsed) <- runRWST (unLC comp) False s
  if M.null $ M.filter isBindingLinear renv
    then return a
    else throwError "Not all linear resources in a computation were consumed"


-- | Uses a resource from the environment, making it unavailable in subsequent computations if it was/consumed a linear resource.
-- If the key doesn't exist, no resources are consumed
use :: (MonadError e m, IsString e) => Var -> LinearCoreT m ()
use key = LinearCoreT do
  mv <- gets (M.lookup key)
  case mv of
    Nothing -> throwError $ fromString $ "Tried to use a linear resource " <> showPprUnsafe key <> " a second time!"
    Just (LambdaBound v)
      | isLinear v -> do
        modify (M.delete key)
        return ()
      | otherwise -> do
        -- If it's an unrestricted variable, we don't remove it from the
        -- environment because it can still be used.

        -- However, we do write it to the used unrestricted/Δ variables if recordingunrestricted is enabled
        shouldRecord <- ask

        if shouldRecord then tell [key]
                        else pure ()

    Just (DeltaBound (UsageEnv env)) -> do
      mapM_ (unLC . use) (M.keys env)


-- | Extend a computation that threads linear resources with a resource that
-- must definitely not escape its scope (i.e. the given computation must
-- consume the resource it was extended with).
--
-- If the resource escapes the given computation, the resulting computation fails.
--
-- If the resource was already in the context it also fails.
extend :: (MonadError e m, IsString e)
       => Var -> IdBinding -> LinearCoreT m a -> LinearCoreT m a
extend key value computation = LinearCoreT do
  gets (M.lookup key) >>= \case
    Just _ -> throwError $ fromString $ "Tried to extend a computation with a resource that was already in the environment: " ++ showPprUnsafe key ++ "."
    Nothing -> do
      modify (M.insert key value)
      result <- unLC computation
      wasConsumed key >>= \case
        Nothing -> return result
        Just m
          | isBindingLinear m
          -> throwError $ fromString $
               "The linear resource " ++ showPprUnsafe key ++ " wasn't consumed in the computation extended with it"
          | otherwise
          -> do
            -- Non linear resource needs to be deleted from scope, or otherwise would escape
            modify (M.delete key)
            return result
  where
    -- Returns 'Nothing' if it was consumed, and Just m otherwise
    wasConsumed x = gets $ (M.lookup x)


-- | Runs a computation that threads linear resources and fails if the
-- computation consumed any resource at all (i.e. fails if the input and output
-- resources are not the same).
--
-- That is, run a computation that does not use linear resources (i.e. an unrestricted computation)
unrestricted :: (MonadError e m, IsString e) => LinearCoreT m a -> LinearCoreT m a
unrestricted computation = LinearCoreT do
  prev <- get
  result <- unLC computation
  after <- get
  when (prev /= after) $
    throwError $ fromString $
      "An unrestricted computation should consume no linear resources, but instead it used " ++ showPprUnsafe (prev M.\\ after) ++ "."
  return result


-- | Run a computation and record the linear resources used in that computation
--
-- In practice, however, we record all resources that were used together with
-- their multiplicity. This is needed if we want to compute the recursive usage
-- environments for a group of recursive lets
record :: (MonadError e m, IsString e) => LinearCoreT m a -> LinearCoreT m (a, M.Map Var Mult)
record computation = LinearCoreT do
  prev <- get
  result <- unLC computation
  after <- get
  let diff = prev M.\\ after
  diffMults <- traverse (\case LambdaBound m -> pure m; DeltaBound _ -> throwError "record: Non linear things disappeared from the context?") diff
  return (result, diffMults)

-- | Count the number of times unrestricted and delta-bound variables in a
-- computation are used.
recordNonLinear :: Monad m => LinearCoreT m a -> LinearCoreT m (a, VarEnv Int)
recordNonLinear comp = LinearCoreT do
  -- We listen to a local computation in which recording flag is true
  (a, w) <- listen $ local (const True) (unLC comp)

  -- Make a usage environment from the number of times some variable is used.
  let w' = FM.listToUFM_C (+) (map (,1) w)
  isRecording <- ask
  if isRecording
     -- We're recording, so we keep everything written so far
     then return (a, w')
     -- We weren't recording when we called this action, which means we're done recording -- erase the writer state
     else pass $ return ((a,w'), \_ -> [])


