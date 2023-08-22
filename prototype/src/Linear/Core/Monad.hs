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
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NE

import Linear.Core.Multiplicities
import GHC.Driver.Ppr (showPprUnsafe)
import qualified Data.Map as M

-- | Computations that thread through a linear context from which resources must
-- be used exactly once, and resources of other multiplicities that can be
-- consumed unrestrictedly
-- (i.e. models computations that are well-defined under a mixed multiplicity context)
--
-- See also 'use' for what using a variable means in these computations
--
-- LinearCoreT
-- * The State, (VarEnv [Mult]), represents the variables in scope. The variables
-- in scope can be linear or non-linear.
--   * When we use a variable that is in scope (see 'use'), we remove it from the
--   list of variables in scope if it was a linear variable
--   * In practice, the state allows threading of resources as per the
--   input/output resource management strategy to typecheck linear types
--   * We store a list of multiplicities because a variable might appear more
--   than once if it has been split, and each multiplicity will be different
--   from each other
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
newtype LinearCoreT m a = LinearCoreT { unLC :: RWST Bool [Var] (M.Map Var (NonEmpty IdBinding)) (ExceptT String m) a }
  deriving (Functor, Applicative, Monad, MonadState (M.Map Var (NonEmpty IdBinding)), MonadError String)

instance Monad m => MonadFail (LinearCoreT m) where
  fail = throwError

runLinearCoreT :: Monad m => M.Map Var IdBinding -> LinearCoreT m a -> m (Either String a)
runLinearCoreT s comp = runExceptT $ do
  (a, renv, _unrestrictedUsed) <- runRWST (unLC comp) False (M.map (:| []) s)
  if M.null $ M.filter (all isBindingLinear) renv
    then return a
    else throwError "Not all linear resources in a computation were consumed"


-- | Uses a resource from the environment, making it unavailable in subsequent computations if it was/consumed a linear resource.
-- If the key doesn't exist, no resources are consumed
use :: Monad m => Var -> LinearCoreT m ()
use = flip use' Nothing where
-- The variable being used might be associated to a tag, in which case we must ensure the resources are split before consumed
-- * The variable will be paired with a tag only in the usage environment of case pattern variables (we recursively invoke this function for usage envs, and that's when the tag exists)
-- * To model this, we receive an explicit multiplicity that the variable should have as an argument
-- * And try to instance a var with the requested multiplicity if it exists, or split a linear variable into multiple tagged vars otherwise
  use' :: Monad m => Var -> Maybe Mult -> LinearCoreT m ()
  use' key _    | isGlobalId key = pure () -- See Note [GlobalId/LocalId]
  use' key mmult = LinearCoreT do
    shouldRecord <- ask
    when shouldRecord $ tell [key]
    mv <- gets (M.lookup key)
    case mv of
      Nothing -> throwError $ fromString $ "Tried to use a linear resource " <> showPprUnsafe key <> " a second time! (Or is it a variable not in scope?)"
      Just ( (LambdaBound mult) :| )
        | isLinear mult -> do -- isLinear looks through tags
          modify (M.delete key)
          case mmult of
            Nothing -> return ()
            Just mmult -> return ()
              -- This variable is likely tagged, so either the variable is
              -- available tagged in the environment, or we have to split the
              -- linear variable
              -- if mmult == mult
              --    then -- hmmm, this Map business is a bit fishy. Maybe the tag should be a property of the variable rather than mult.
                 -- how can we have multiple vars with the same name?
        | otherwise -> do
          -- If it's an unrestricted variable, we don't remove it from the
          -- environment because it can still be used.
          -- We don't split it either or look at the tag. We don't have to care
          -- because it's unrestricted.
          return ()
      Just ( DeltaBound (UsageEnv env):|[] )-> do
        -- Record the usage of the delta bound var, but not the usages of the
        -- underlying vars
        local (const False) $
          mapM_ (unLC . go) env
            where
              go (v, Tagged t m) = use' v (Just (Tagged t m))
              go (v, _) = use' v Nothing
      Just ( DeltaBound _:|_ ) -> error "impossible, shouldn't happen"


-- | Extend a computation that threads linear resources with a resource that
-- must definitely not escape its scope (i.e. the given computation must
-- consume the resource it was extended with).
--
-- If the resource escapes the given computation, the resulting computation fails.
--
-- If the resource was already in the context it also fails.
extend :: Monad m
       => Var -> IdBinding -> LinearCoreT m a -> LinearCoreT m a
extend key value computation = LinearCoreT do
  gets (M.lookup key) >>= \case
    Just _ -> throwError $ fromString $ "Tried to extend a computation with a resource that was already in the environment: " ++ showPprUnsafe key ++ "."
    Nothing -> do
      modify (M.insert key (value :| []))
      result <- unLC computation
      wasConsumed key >>= \case
        Nothing -> return result
        Just ms
          | any isBindingLinear ms
          -> throwError $ fromString $
               "The linear resource " ++ showPprUnsafe key ++ " wasn't fully consumed in the computation extended with it. [" ++ showPprUnsafe ms ++ "]"
          | otherwise
          -> do
            -- Non linear resource needs to be deleted from scope, or otherwise would escape
            modify (M.delete key)
            return result
  where
    -- Returns 'Nothing' if it was consumed, and Just m otherwise
    wasConsumed x = gets $ (M.lookup x)

-- | 'extend' multiple variables
extends :: Monad m => [(Var, IdBinding)] -> LinearCoreT m a -> LinearCoreT m a
extends [] comp = comp
extends ((v,b):bs) comp = extend v b $ extends bs comp

-- | 'drop' resources listed in a usage environment from the available resources in the computation
drop :: Monad m => UsageEnv -> LinearCoreT m a -> LinearCoreT m a
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
unrestricted :: Monad m => LinearCoreT m a -> LinearCoreT m a
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
record :: Monad m => LinearCoreT m a -> LinearCoreT m (a, UsageEnv)
record computation = LinearCoreT do
  prev :: M.Map Var (NonEmpty IdBinding) <- get
  result <- unLC computation
  after <- get
  let diff = prev M.\\ after
  diffMults <- traverse (traverse (\case LambdaBound m -> pure m; DeltaBound _ -> throwError "record: Non linear things disappeared from the context?")) diff
  return (result, UsageEnv (joinMs $ M.toList diffMults))
    where
      joinMs :: [(Var, NonEmpty Mult)] -> [(Var, Mult)]
      joinMs = foldr (\(v,ms) -> (map (v,) (NE.toList ms) ++)) []

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


