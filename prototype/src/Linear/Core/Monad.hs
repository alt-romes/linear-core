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
  , extends
  , drop
  , unrestricted
  , record
  , recordAll
  )
  where

import Prelude hiding (drop)
import Control.Monad
import Data.String
import Control.Monad.State
import Control.Monad.RWS.CPS
import Control.Monad.Except
import GHC.Types.Var

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
  deriving (Functor, Applicative, Monad, MonadTrans, MonadFail, MonadState (M.Map Var IdBinding))

runLinearCoreT :: (MonadError e m, IsString e) => M.Map Var IdBinding -> LinearCoreT m a -> m a
runLinearCoreT s comp = do
  (a, renv, _unrestrictedUsed) <- runRWST (unLC comp) False s
  if M.null $ M.filter isBindingLinear renv
    then return a
    else throwError "Not all linear resources in a computation were consumed"


-- | Uses a resource from the environment, making it unavailable in subsequent computations if it was/consumed a linear resource.
-- If the key doesn't exist, no resources are consumed
use :: (MonadError e m, IsString e) => Var -> LinearCoreT m ()
use key | isGlobalId key = pure () -- See Note [GlobalId/LocalId]
use key = LinearCoreT do
  shouldRecord <- ask
  when shouldRecord $ tell [key]
  mv <- gets (M.lookup key)
  case mv of
    Nothing -> throwError $ fromString $ "Tried to use a linear resource " <> showPprUnsafe key <> " a second time! (Or is it a variable not in scope?)"
    Just (LambdaBound v)
      | isLinear v -> do
        modify (M.delete key)
        return ()
      | otherwise -> do
        -- If it's an unrestricted variable, we don't remove it from the
        -- environment because it can still be used.
        return ()
    Just (DeltaBound (UsageEnv env)) -> do
      -- Record the usage of the delta bound var, and not the usages of the
      -- underlying vars
      local (const False) $
        mapM_ (unLC . use) (map fst env)


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

-- | 'extend' multiple variables
extends :: (MonadError e m, IsString e) => [(Var, IdBinding)] -> LinearCoreT m a -> LinearCoreT m a
extends [] comp = comp
extends ((v,b):bs) comp = extend v b $ extends bs comp

-- | 'drop' resources listed in a usage environment from the available resources in the computation
drop :: (MonadError e m, IsString e) => UsageEnv -> LinearCoreT m a -> LinearCoreT m a
drop (UsageEnv env) comp = do
  prev <- LinearCoreT get
  -- Remove (don't consume!) resources ocurring in the given usage env from the available resources, then run the computation
  _ <- modify (M.\\ (M.fromList env))
  a <- comp
  -- Restore resources
  LinearCoreT (put prev)
  return a

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
record :: (MonadError e m, IsString e) => LinearCoreT m a -> LinearCoreT m (a, UsageEnv)
record computation = LinearCoreT do
  prev <- get
  result <- unLC computation
  after <- get
  let diff = prev M.\\ after
  diffMults <- traverse (\case LambdaBound m -> pure m; DeltaBound _ -> throwError "record: Non linear things disappeared from the context?") diff
  return (result, UsageEnv (M.toList diffMults))

-- | Count the number of times linear, unrestricted, and delta-bound variables in a computation are used.
recordAll :: Monad m => LinearCoreT m a -> LinearCoreT m (a, M.Map Var Int)
recordAll comp = LinearCoreT do
  -- We listen to a local computation in which recording flag is true
  (a, w) <- listen $ local (const True) (unLC comp)

  -- Make a usage environment from the number of times some variable is used.
  let w' = M.fromListWith (+) (map (,1) w)
  isRecording <- ask
  if isRecording
     -- We're recording, so we keep everything written so far
     then return (a, w')
     -- We weren't recording when we called this action, which means we're done recording -- erase the writer state
     else pass $ return ((a,w'), \_ -> [])


