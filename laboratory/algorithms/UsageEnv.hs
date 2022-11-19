{-# LANGUAGE LambdaCase #-}
module UsageEnv where

import Data.Maybe
import qualified Data.Map.Internal as M

type Var  = String
type Mult = Int
type UsageEnv = M.Map Var Mult


computeRecUsageEnvs :: [(Var, UsageEnv)] -- ^ Recursive usage environments associated to their recursive call
                    -> [(Var, UsageEnv)] -- ^ Non-recursive usage environments
computeRecUsageEnvs l =
  foldl (flip $ \(v,vEnv) -> map $ \(n, nEnv) ->
      (n, ((fromMaybe 0 $ v `M.lookup` nEnv) `scale` (M.delete v vEnv)) `sup` (M.delete v nEnv))) l l

sup :: UsageEnv -> UsageEnv -> UsageEnv
sup = M.merge M.preserveMissing M.preserveMissing (M.zipWithMatched $ \_ x y -> max x y)
  
scale :: Mult -> UsageEnv -> UsageEnv
scale m = M.map (*m)

