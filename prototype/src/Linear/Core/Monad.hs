{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE ViewPatterns #-}
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
  , drop, dropEnvOf
  , unrestricted
  , record
  , dryRun

  , makeEnvResourcesIrrelevant
  , withSameEnvMap
  , setTopLevelBindingName

  -- * Utils
  , restoringState
  , LCState
  )
  where

import qualified GHC.Core.Type
import Prelude hiding (drop)
import qualified Data.Set as S
import Control.Monad
import Data.String
import Control.Monad.State
import GHC.Prelude (pprTraceM, pprTrace)
import qualified GHC.Utils.Outputable as Ppr
import Control.Monad.RWS.CPS
import Control.Monad.Except
import GHC.Types.Var
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NE

import Linear.Core.Multiplicities
import GHC.Driver.Ppr (showPprUnsafe)
import qualified Data.Map as M
import qualified GHC.Utils.Panic as Ppr
import qualified Data.List as L
import Data.Either (fromRight)
import Data.Bifunctor (Bifunctor(..))
import Data.Maybe (catMaybes)

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
-- computation, including the unrestricted variables (now [(Var, Mult)] because we record fragment uses).
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
newtype LinearCoreT m a = LinearCoreT { unLC :: RWST (IsDryRun, AllowIrrelevant, BindingName)
                                                     [(Var, Mult)]
                                                     LCState
                                                     (ExceptT String m) a }
  deriving (Functor, Applicative, Monad, MonadState LCState, MonadReader (IsDryRun,AllowIrrelevant,BindingName))
-- should have been a state machine based impl

-- | We track the name of the top-level binding to use in Error Messages
type BindingName = String

-- | The linear core state represents the resources available in a computation.
-- Each resource might be either LambdaBound, DeltaBound, or be partially
-- consumed, in which case it used to be lambda bound but is now fragmented
-- into a set of tagged resources, represented by a non-empty list of (tagged) multiplicities
type LCState = M.Map Var (Either IdBinding (NonEmpty Mult))

-- | If we're doing a dry run we do two things:
-- * Record the amount of times a linear variable is used
-- * Don't fail if the linear variable is used twice
-- Thus they are never removed from the context, and just used to check how many
-- times they would be consumed were we to typecheck for real. This is used when
-- inferring usage environments for recursive bindings.
type IsDryRun = Bool

instance Monad m => MonadError String (LinearCoreT m) where
  throwError str = LinearCoreT do
    (_,_,name) <- ask
    lift $ throwError (name <> ": " <> str)

instance Monad m => MonadFail (LinearCoreT m) where
  fail = throwError

runLinearCoreT :: Monad m => M.Map Var IdBinding -> LinearCoreT m a -> m (Either String a)
runLinearCoreT s comp = runExceptT $ do
  (a, renv, _unrestrictedUsed) <- runRWST (unLC comp) (False, DisallowIrrelevant,"MonadFail messages weren't improved in the end") (M.map Left s)
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
    -- When recording, we count when linear resources are used, and allow them
    -- to be consumed more than once (despite that not being possible if we were
    -- typechecking).
    (isDryRun, allowsIrrelevant, _) <- ask

    -- Lookup the variable in the environment
    mv <- gets (M.lookup key)

    -- pprTraceM "Using var" (Ppr.ppr key Ppr.<+> Ppr.text "with mult" Ppr.<+>
    --   Ppr.ppr mv Ppr.<+> Ppr.text "and tag environment" Ppr.<+> Ppr.ppr mtags
    --   Ppr.<+> Ppr.text "; allowIrr: " Ppr.<+> Ppr.text (show allowsIrrelevant))


    case mv of

      -- Variable has already been consumed (it should be guaranteed to be in scope since Core programs are well-typed)
      Nothing -> do
        lcstate <- get
        throwError $
          "Tried to use a linear resource "
            <> showPprUnsafe key
            <> " a second time! (Or is it a variable not in scope?)"
            <> "\nLC State:\n"
            <> showPprUnsafe lcstate

      -- Resource is LambdaBound and hasn't been neither consumed nor split
      Just (Left (LambdaBound mult))

        -- Resource is linear
        | isLinear mult -- isLinear looks through tags, but top level lambda-bound should never have tags anyway
        -> do
          when (allowsIrrelevant == DisallowIrrelevant && isIrrelevant mult) $
             throwError $ fromString $ "Tried to use an irrelevant linear resource " <> showPprUnsafe key <> " directly!"

          case mtags of
            -- We aren't trying to use a fragment of this resource,
            -- so it is simply consumed
            [] ->
              if isDryRun
                 then tell [(key, mult)]
                 else do
                   -- pprTraceM "Using lambda bound" (Ppr.ppr key Ppr.<+> Ppr.ppr mult)
                   modify (M.delete key)

            -- We are trying to use a fragment of this resource, so we split it
            -- as necessary according to the tag stack until we can consume the
            -- given tag (in the form of a tagstack)
            tags -> do
              (splits, consumed_frag) <- splitAsNeededThenConsume allowsIrrelevant tags mult
              -- pprTraceM "Splitting key at tags" (Ppr.ppr key Ppr.<+> Ppr.ppr tags Ppr.<+> Ppr.ppr splits)
              if isDryRun
                 then tell [(key, consumed_frag)]
                 else case NE.nonEmpty splits of
                    Nothing -> do
                        -- pprTraceM "Using lambda bound split" (Ppr.ppr key)
                        modify (M.delete key) -- we split the fragment and consumed the only one
                    Just splits'  -> do
                      modify (M.insert key (Right splits')) -- we keep the remaining fragments

        -- Resource is unrestricted
        | otherwise -> do
          -- If it's an unrestricted variable, we don't remove it from the
          -- environment because it can still be used.
          -- We don't split it either or look at the tag. We don't have to care
          -- because it's unrestricted.
          return ()

      -- Resource is DeltaBound
      Just (Left (DeltaBound (UsageEnv env))) -> do

        -- Simply recurse to use all variables from the usage environment, but
        -- allow irrelevant resources to occur, since we're using resources from
        -- within a usage environment
        local (\(idr,_,n) -> (idr, AllowIrrelevant,n)) $
          mapM_ (unLC . go) env
            where
              go (v, m) = use' v (extractTags m)

      -- We can't allow consuming irrelevant tagged resources directly
      -- Resource was LambdaBound but has been split into a set of tagged resources which haven't yet been consumed
      Just (Right mults) -> do
        case mtags of
          -- We have no tags but trying to use a fragmented resource. Nope.
          [] -> throwError "Trying to consume a resource that has been fragmented as a whole resource"

          -- We have a tagstack, so we split and consume as needed all the mults,
          -- In practice, this will consume (or further fragment as need) just
          -- the one resource from the group of fragmented multiplicities, and
          -- non-matching tagged fragments untouched.
          tags -> do

            (join -> splits, catMaybes -> consumed_ms)
              <- mapAndUnzipM (\m -> if extractTags m `L.isPrefixOf` tags
                                        -- if the mult doesn't match the prefix then we don't split, otherwsie we split things that are definitely not supposed to split!
                                        then second Just <$> splitAsNeededThenConsume allowsIrrelevant tags m
                                        else return ([m], Nothing)) (NE.toList mults)
            -- pprTraceM "Split key at tags" (Ppr.ppr key Ppr.<+> Ppr.ppr tags Ppr.<+> Ppr.ppr splits)
            if isDryRun
               then tell (map (key,) consumed_ms) -- Again, we don't consume things when dry run
               else case NE.nonEmpty splits of
                Nothing -> do
                    -- pprTraceM "Using last lambda bound split" (Ppr.ppr key)
                    modify (M.delete key) -- OK, we only had one fragment left and consumed it
                Just splits' -> modify (M.insert key (Right splits'))   -- we keep the remaining fragments

    -- key_val <- gets (M.lookup key)
    -- pprTraceM "Used var, remaining var in env is:" (Ppr.ppr key Ppr.<+> Ppr.ppr key_val)


-- | Extend a computation that threads linear resources with a resource that
-- must definitely not escape its scope (i.e. the given computation must
-- consume the resource it was extended with).
--
-- If the resource escapes the given computation, the resulting computation fails.
--
-- If the resource was already in the context it also fails.
extend :: forall m a. Monad m
       => BindSite -- ^ for error messages
       -> Var -> IdBinding -> LinearCoreT m a -> LinearCoreT m a
extend bindsite key value computation = LinearCoreT do
  didShadow <- gets (M.lookup key) >>= \case
    Just vl -> do
      -- We override each local top-level binding when we typecheck them individually
      -- but return it, so it can be reset to after the extension (otherwise it would be deleted)
      -- Later: Some case binders in Core really seem to use the same name.
      -- So we basically implement shadowing sort of (extend with new thing, but recall the old thing after extended computation)
      return (Just vl)
      --   throwError $ fromString $
      --     "Tried to extend a computation with a resource that was already in the environment: " ++ showPprUnsafe (key,value) ++ "; Binder: " ++ show bindsite
    Nothing -> do
      return Nothing
  modify (M.insert key (Left value))
  result <- pass $ (,cleanboundf) <$> unLC computation
  (isDryRun, _, _) <- ask
  res <- wasConsumed key >>= \case
    Nothing -> return result
    Just ms
      | either isBindingLinear (const True) ms
      , not isDryRun -- When doing a dry run, don't fail, even if the resource isn't consumed
      -> do
        lcs <- get
        throwError $ fromString $
           "The linear resource " ++ showPprUnsafe key ++ " wasn't fully consumed in the computation extended with it. [" ++ showPprUnsafe ms ++ "]; Binder: " ++ show bindsite ++ "\nLCState:" ++ showPprUnsafe lcs
      | otherwise
      -> do
        -- Non linear resource needs to be deleted from scope, or otherwise would escape
        -- (or this is a linear resource unused in a dry run)
        modify (M.delete key)
        return result

  case didShadow of
    Nothing -> return res
    Just vl -> do
      modify (M.insert key vl)
      return res
  where
    -- Returns 'Nothing' if it was consumed, and Just m otherwise
    wasConsumed :: forall m'. MonadState LCState m' => Var -> m' (Maybe (Either IdBinding (NonEmpty Mult)))
    wasConsumed x = gets (M.lookup x)

    -- extremely contrived but no time to do this well we remove all occurrences
    -- of variables bound inside a dry run computation, since we only care about
    -- recording free linear variables in the binders.
    -- It might seem as we don't check if these variables are used linearly, but we do when we type the let binders a second time with the correct usage environments.
    -- The dry run info (the writer state) is really only about recording stuff to construct the environments. Then we type as usual using those envs.
    -- But only for lambda bound things... or otherwise we'd delete the same let binders we are trying to type out of the environment
    cleanboundf = filter (\wr -> bindsite == LambdaBinder && fst wr /= key)

-- | 'extend' multiple variables
extends :: Monad m => BindSite -> [(Var, IdBinding)] -> LinearCoreT m a -> LinearCoreT m a
extends _ [] comp = comp
extends bsite ((v,b):bs) comp = extend bsite v b $ extends bsite bs comp

-- | 'drop' resources listed in a usage environment from the available resources in the computation
drop :: Monad m => UsageEnv -> LinearCoreT m ()
drop (UsageEnv env) = do

  -- Remove resources ocurring in the given usage env from the available resources, then run the computation
  modify (`diffResources` (M.fromListWith (\cases (Right ne1) (Right ne2) -> Right (ne1 <> ne2) ;  _ _ -> error "No left left, left right, or right left") $ L.map (\(v,m) -> if null (extractTags m) then (v, Left (LambdaBound m)) else (v, Right (NE.fromList [m]))) env))

dropEnvOf :: Monad m
          => Var -- ^ The var to make unrestricted by "dropping all resources from it"
          -> LinearCoreT m ()
dropEnvOf v = do
  modify (M.insert v (Left (LambdaBound (Relevant GHC.Core.Type.ManyTy))))




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
-- Linear resources must be used linearly or otherwise the computation
-- will fail; if you're trying to count how many times a linear resource is used
-- without failing, see 'dryRun'
--
-- If you mean to restore the resources consumed in this computation, you must
-- do so manually (e.g. using 'restoringResources')
record :: Monad m => LinearCoreT m a -> LinearCoreT m (a, UsageEnv)
record computation = LinearCoreT do
  prev   <- get
  result <- unLC computation
  after  <- get
  let diff = diffResources prev after
  diffMults <- extractDiffMults diff
  -- pprTraceM "prev after and diff" (Ppr.ppr diffMults) -- Ppr.<+> Ppr.ppr prev Ppr.<+> Ppr.ppr after)
  return (result, UsageEnv diffMults)
    where
      extractDiffMults :: forall m. MonadError String m => M.Map Var (Either IdBinding (NonEmpty Mult)) -> m [(Var, Mult)]
      extractDiffMults diffs = concat <$>
        traverse (\case (_, Left (DeltaBound _)) -> throwError "record: Non linear things disappeared from the context?"
                        (v, Left (LambdaBound m)) -> pure [(v, m)]
                        (v, Right mults) -> pure $ map (v,) $ NE.toList mults
                ) (M.toList diffs)

-- Return the a difference (akin to set difference) from two group of resources, accounting for splits
-- e.g.
-- e.g. [(x,One#(,)2)] `diffResources` [(x,One#(,)2#(#,#)2)] == [(x,One#(,)2#(#,#)1)]
diffResources :: LCState -> LCState -> LCState
diffResources = M.differenceWith diffgo
    where
      diffgo :: Either IdBinding (NonEmpty Mult)
             -> Either IdBinding (NonEmpty Mult)
             -> Maybe (Either IdBinding (NonEmpty Mult))
      diffgo (Left _) (Left _)  = Nothing -- for left bindings, equal keys means something wasn't used (thus not relevant in the diff)
      diffgo (Left (LambdaBound m)) (Right (NE.toList -> ne)) = Right <$> NE.nonEmpty ([m] `setDiffAwareOfSplits` ne) -- we might delete the resource if the split has just 1 position
      diffgo (Left (DeltaBound _)) (Right _) = error "How would that happen? DB"
      diffgo (Right _) (Left _) = error "How would that happen?"
      diffgo (Right (NE.toList -> ne1)) (Right (NE.toList -> ne2)) = Right <$> NE.nonEmpty (ne1 `setDiffAwareOfSplits` ne2)

      -- e.g. [One#(,)2] `setDiffAwareOfSplits` [One#(,)2#(#,#)2] == [One#(,)2#(#,#)1]
      setDiffAwareOfSplits :: [Mult] -> [Mult] -> [Mult]
      setDiffAwareOfSplits = foldl (flip godelete) where
        godelete :: Mult -> [Mult] -> [Mult]
        godelete _ [] = []
        godelete x (y:ys)
          | x == y
          = ys
          | extractTags y `L.isPrefixOf` extractTags x
          = case splitAsNeededThenConsume AllowIrrelevant (extractTags x) y of
              Left string -> error string
              Right (res,_wasconsumed) -> res ++ ys -- the one that was consumed is deleted, but not the remaining resources
          | otherwise
          = y : godelete x ys

-- | Count the number of times *free* linear variables in a computation are
-- consumed.  This doesn't ever make the computation fail because of linearity
-- because we disable checking. It's a dry run, only useful to determine if
-- certain things are going to be used more than once (in particular for the
-- recursive usage environment inference algorithm)
dryRun :: Monad m => LinearCoreT m a -> LinearCoreT m (a, M.Map Var Int)
dryRun comp = LinearCoreT do
  (isRecording, _, _) <- ask

  -- We listen to a local computation in which recording flag is true
  pass $ do
    (a, S.toList . S.fromList . map fst -> w) <- listen $ local (\(_,irr,n) -> (True,irr,n)) (unLC comp)
    -- Make a usage environment from the number of times some variable is used.
    let w' = M.fromListWith (+) (map (,1) w)
    let cleanf ww = if isRecording
                     -- We're recording, so we keep everything written so far
                     then ww
                     -- We weren't recording when we called this action, which means we're done recording -- erase the writer state
                     else []
    return ((a,w'), cleanf)

      --- ^ we take only unique ocurrences of the whole var I guess...


makeEnvResourcesIrrelevant :: Monad m => UsageEnv -> LinearCoreT m ()
makeEnvResourcesIrrelevant (UsageEnv vs) = do
  -- pprTraceM "Making resource irrelevant in case alternative" $! Ppr.empty
  lcstate0 <- get
  lcstate1 <- forM vs $ \(var,mult) -> do
    case M.lookup var lcstate0 of
      Nothing -> error "This shouldn't be possible! How does the usage env refer to variables out of scope?"
      Just (Left (LambdaBound m))
        | mult == m -> pure (var, Left (LambdaBound (makeMultIrrelevant m)))
        | otherwise
        -> do
          -- We might reach this situation if the resource being consumed has
          -- been split and its usage environment reflects this; but we restored the state (hence re-put the unsplit resource)
          -- We can simply keep the unsplit resource, as later uses of the split resource will split as needed again.
          pure (var, Left (LambdaBound (makeMultIrrelevant m)))
      Just (Left (DeltaBound env')) -> pure (var, Left (DeltaBound $ makeIrrelevant env'))
      Just (Right mults) -> pure (var, Right $ NE.map (\x -> if x == mult then makeMultIrrelevant x else x) mults)
  -- pprTraceM "mkEnvResIrr lcstate0" (Ppr.ppr lcstate0)
  -- pprTraceM "mkEnvResIrr lcstate1" (Ppr.ppr lcstate1)
  put (M.fromList lcstate1 <> lcstate0)
  -- pprTraceM "Made resources irrelevant in case alternative" $! Ppr.empty

-- | Run a list of monadic computation ala 'mapM' but restoring the typing environment
-- for each individual action
withSameEnvMap :: Monad m => (a -> LinearCoreT m b) -> [a] -> LinearCoreT m [b]
withSameEnvMap f ls = LinearCoreT do
  lcstate <- get
  (ls', states) <- mapAndUnzipM (\x -> put lcstate >> unLC (f x) >>= \y -> gets (y,)) ls
  unless (allEq states) $
    throwError $ "withSameEnvMap: Not all eq!" ++ Ppr.showPprUnsafe (fmap (M.filter (\case Left (DeltaBound _) -> False; _ -> True)) states)
  return ls'


restoringState :: Monad m => LinearCoreT m a -> LinearCoreT m a
restoringState act = do
  s <- get
  a <- act
  put s
  return a

setTopLevelBindingName :: Monad m => BindingName -> LinearCoreT m a -> LinearCoreT m a
setTopLevelBindingName bn = local (\(a,b,_) -> (a,b,bn))

allEq :: Eq a => [a] -> Bool
allEq = allEq' Nothing where
  allEq' _        []     = True
  allEq' Nothing  (x:xs) = allEq' (Just x) xs
  allEq' (Just y) (x:xs) = x == y && allEq' (Just y) xs
  
