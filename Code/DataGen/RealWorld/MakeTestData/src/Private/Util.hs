module Private.Util where

import           Control.Arrow
import           Data.List (foldl')
import qualified Data.Set as S

-- Compute all partitions of a list into a list of k elements and a list of n - k elements
partitionK :: [t] -> Int -> [([t], [t])]
xs     `partitionK` 0 = [([], xs)]
[]     `partitionK` _ = []
(x:xs) `partitionK` k = pickX ++ dontPickX
  where pickX     = map (first  (x:)) (xs `partitionK` (k-1))
        dontPickX = map (second (x:)) (xs `partitionK`  k)

-- Choose sublists of k elements from a list of length n
choose :: [t] -> Int -> [[t]]
xs `choose` k = map fst (xs `partitionK` k)

-- A monadic unfold (why is there no such thing in Control.Monad?)
unfoldM :: Monad m => (a -> m (Maybe (b, a))) -> a -> m [b]
unfoldM f = go
  where go seed = do next <- f seed
                     case next of
                       Nothing         -> return []
                       Just (x, seed') -> (x :) <$> go seed'

-- Break the second list into groups of lengths given in the first list
groups :: [Int] -> [t] -> [[t]]
groups [] _      = []
groups (g:gs) xs = y : ys
  where (y, xs') = splitAt g xs
        ys       = groups gs xs'

-- Union a list of sets together
union :: Ord t => [S.Set t] -> S.Set t
union = foldl' S.union S.empty
