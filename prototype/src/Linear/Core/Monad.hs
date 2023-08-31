{-# LANGUAGE MultiWayIf #-}
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
newtype LinearCoreT m a = LinearCoreT { unLC :: RWST Bool [Var] LCState (ExceptT String m) a }
  deriving (Functor, Applicative, Monad, MonadState LCState, MonadError String)

-- | The linear core state represents the resources available in a computation.
-- Each resource might be either LambdaBound, DeltaBound, or be partially
-- consumed, in which case it used to be lambda bound but is now fragmented
-- into a set of tagged resources, represented by a non-empty list of (tagged) multiplicities
type LCState = M.Map Var (Either IdBinding (NonEmpty Mult))

instance Monad m => MonadFail (LinearCoreT m) where
  fail = throwError

runLinearCoreT :: Monad m => M.Map Var IdBinding -> LinearCoreT m a -> m (Either String a)
runLinearCoreT s comp = runExceptT $ do
  (a, renv, _unrestrictedUsed) <- runRWST (unLC comp) False (M.map Left s)
  -- All linear IdBindings must be consumed, and no fragments may remain
  if M.null $ M.filter (either isBindingLinear (const True)) renv
    then return a
    else throwError "Not all linear resources in a computation were consumed"

-- All this state management is a bit complex, i wonder if it would be simpler if defined in terms of e.g. finite automata

-- | Uses a resource from the environment, making it unavailable in subsequent computations if it was/consumed a linear resource.
-- If the key doesn't exist, no resources are consumed
use :: Monad m => Var -> LinearCoreT m ()
use = flip use' [] where

  -- | Variables in the being used might be associated to a tag, in which case we must ensure the resources are split before consumed
  use' :: Monad m => Var -> [Tag] -> LinearCoreT m ()
  use' key _    | isGlobalId key = pure () -- See Note [GlobalId/LocalId]; Global ids are top-level imported Ids, which are unrestricted
  use' key mtags = LinearCoreT do

    -- When recording, we eagerly write the variable used
    shouldRecord <- ask
    when shouldRecord $ tell [key]

    -- Lookup the variable in the environment
    mv <- gets (M.lookup key)
    case mv of

      -- Variable has already been consumed (it should be guaranteed to be in scope since Core programs are well-typed)
      Nothing -> throwError $ fromString $ "Tried to use a linear resource " <> showPprUnsafe key <> " a second time! (Or is it a variable not in scope?)"


      -- Resource is LambdaBound and hasn't been neither consumed nor split
      Just (Left (LambdaBound mult))

        -- Resource is linear
        | isLinear mult -- isLinear looks through tags, but top level lambda-bound should never have tags anyway
        -> do
          case mtags of
            -- We aren't trying to use a fragment of this resource,
            -- so it is simply consumed
            [] -> modify (M.delete key)

            -- We are trying to use a fragment of this resource, so we split it
            -- as necessary according to the tag stack until we can consume the
            -- given tag (in the form of a tagstack)
            tags -> let splits = splitAsNeededThenConsume tags mult
                     in case NE.nonEmpty splits of
                          Nothing      -> modify (M.delete key) -- we split the fragment and consumed the only one
                          Just splits' -> modify (M.insert key (Right splits')) -- we keep the remaining fragments

        -- Resource is unrestricted
        | otherwise -> do
          -- If it's an unrestricted variable, we don't remove it from the
          -- environment because it can still be used.
          -- We don't split it either or look at the tag. We don't have to care
          -- because it's unrestricted.
          return ()

      -- Resource is DeltaBound
      Just (Left (DeltaBound (UsageEnv env))) -> do
        -- Record the usage of the delta bound var, but not the usages of the
        -- underlying vars, i.e. disable recording
        local (const False) $
          mapM_ (unLC . go) env
            where
              go (v, m) = use' v (extractTags m)

      -- Resource was LambdaBound but has been split into a set of tagged resources which haven't yet been consumed
      Just (Right mults) -> do
        case mtags of
          -- We have no tags but trying to use a fragmented resource. Nope.
          [] -> throwError "Trying to consume a resource that has been fragmented as a whole resource"

          -- We have a tagstack, so we split and consume as needed all the mults,
          -- In practice, this will consume (or further fragment as need) just
          -- the one resource from the group of fragmented multiplicities, and
          -- non-matching tagged fragments untouched.
          tags -> let splits = concatMap (splitAsNeededThenConsume tags) (NE.toList mults)
                   in case NE.nonEmpty splits of
                        Nothing      -> modify (M.delete key) -- OK, we only had one fragment left and consumed it
                        Just splits' -> modify (M.insert key (Right splits'))   -- we keep the remaining fragments


-- | Extend a computation that threads linear resources with a resource that
-- must definitely not escape its scope (i.e. the given computation must
-- consume the resource it was extended with).
--
-- If the resource escapes the given computation, the resulting computation fails.
--
-- If the resource was already in the context it also fails.
extend :: forall m a. Monad m
       => Var -> IdBinding -> LinearCoreT m a -> LinearCoreT m a
extend key value computation = LinearCoreT do
  gets (M.lookup key) >>= \case
    Just _ -> throwError $ fromString $ "Tried to extend a computation with a resource that was already in the environment: " ++ showPprUnsafe key ++ "."
    Nothing -> do
      modify (M.insert key (Left value))
      result <- unLC computation
      wasConsumed key >>= \case
        Nothing -> return result
        Just ms
          | either isBindingLinear (const True) ms
          -> throwError $ fromString $
               "The linear resource " ++ showPprUnsafe key ++ " wasn't fully consumed in the computation extended with it. [" ++ showPprUnsafe ms ++ "]"
          | otherwise
          -> do
            -- Non linear resource needs to be deleted from scope, or otherwise would escape
            modify (M.delete key)
            return result
  where
    -- Returns 'Nothing' if it was consumed, and Just m otherwise
    wasConsumed :: forall m'. MonadState LCState m' => Var -> m' (Maybe (Either IdBinding (NonEmpty Mult)))
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
  prev :: LCState <- get
  result <- unLC computation
  after <- get
  let diff = prev M.\\ after
  diffMults <- extractDiffMults diff
  return (result, UsageEnv diffMults)
    where
      extractDiffMults :: forall m. MonadError String m => M.Map Var (Either IdBinding (NonEmpty Mult)) -> m [(Var, Mult)]
      extractDiffMults diffs = concat <$>
        traverse (\case (_, Left (DeltaBound _)) -> throwError "record: Non linear things disappeared from the context?"
                        (v, Left (LambdaBound m)) -> pure [(v, m)]
                        (v, Right mults) -> pure $ map (v,) $ NE.toList mults
                ) (M.toList diffs)

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

