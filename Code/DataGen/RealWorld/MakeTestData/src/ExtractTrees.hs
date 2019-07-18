module ExtractTrees ( extractTrees
                    , Stats(..)
                    ) where

import           Control.Arrow
import           Control.Monad.Trans.State (runState, state)
import           Data.List (foldl', partition)
import qualified Data.Map.Strict as M
import           Data.Maybe (fromJust)
import qualified Data.Set as S
import qualified PQ
import           Tree

-- Analyze the collection of trees to extract a hopefully large collection of subtrees with
-- the given number of leaves.
extractTrees :: (Ord t, Show t) => Int -> [Tree t] -> IO (Stats, [Tree t])
extractTrees leafCount trees = do putStrLn "Counting leaf frequencies"
                                  let leafFreqs = makeLeafFreqs trees

                                  leafFreqs `seq` putStrLn "Selecting leaves and trees that contain them"
                                  let (selectedLeaves, selectedTrees) = pickLeaves leafCount trees leafFreqs

                                  selectedLeaves `seq` putStrLn "Pruning selected trees to selected leaves"
                                  let prunedTrees = selectedTrees `prunedTo` selectedLeaves

                                  prunedTrees `seq` putStrLn "Resolving multifurcations"
                                  let binaryTrees = binaryResolutionsOf prunedTrees

                                  binaryTrees `seq` putStrLn "Discarding duplicate trees"
                                  let dedupedTrees = S.elems $ S.fromList binaryTrees

                                  let -- Collect various statistics about the input and output
                                      stats = Stats { numInTrees         = length trees
                                                    , numInLabels        = PQ.size leafFreqs
                                                    , numOutTrees        = length dedupedTrees
                                                    , numOutLabels       = leafCount
                                                    , numMultifurcations = multiCount
                                                    , minNodeDegree      = minDeg
                                                    , maxNodeDegree      = maxDeg
                                                    , labelSetOk         = correctLabels
                                                    , restrictionsOk     = correctRestrictions
                                                    }

                                      -- The number of multifurcations in the selected trees
                                      multiCount = sum $ map numberOfMultifurcationsIn prunedTrees

                                      -- The minimum and maximum degree of internal nodes
                                      minDeg             = minimum minDegs
                                      maxDeg             = maximum maxDegs
                                      (minDegs, maxDegs) = unzip $ map minmaxNodeDegreesOf dedupedTrees

                                      -- Are the computed trees correct restrictions to the chosen label set?
                                      correctLabels       = all (selectedLeaves `isLabelSetOf`) dedupedTrees
                                      correctRestrictions = all (uncurry isRestrictionOf) (zip prunedTrees selectedTrees)

                                  -- Return the final result
                                  return (stats, dedupedTrees)

-- Count how often each leaf appears in all the trees
makeLeafFreqs :: Ord t => [Tree t] -> PQ.PQ Int t
makeLeafFreqs trees = PQ.fromList
                    $ M.toList $ M.fromListWith (+)
                    $ zip (concatMap (S.toList . labelSetOf) trees) (repeat 1)

-- Heuristically pick a subset of leafCount leaves that is contained in many trees.
-- Return the chosen set of leaves and the trees that contain all of them.
pickLeaves :: Ord t => Int -> [Tree t] -> PQ.PQ Int t -> (S.Set t, [Tree t])
pickLeaves leafCount =
  curry $ (map (id &&& labelSetOf) *** id)                           >>>
          runState (sequence $ replicate leafCount $ state pickLeaf) >>>
          (S.fromList *** map fst . fst)

type S t = ([(Tree t, S.Set t)], PQ.PQ Int t)

-- Pick and remove the most frequent leaf, update the occurrence counts of the leaves
pickLeaf :: Ord t => S t -> (t, S t)
pickLeaf (treesAndLeaves, leafFreqs) = (leaf, (ins, leafFreqs''))
  where ((leaf, _), leafFreqs') = PQ.deleteMax leafFreqs
        (ins, outs)             = partition (S.member leaf . snd) treesAndLeaves
        rmLeaves                = concatMap (S.toList . snd) outs
        leafFreqs''             = foldl' removeLeaf leafFreqs' rmLeaves

-- Record the removal of a leaf in the priority queue of leaf frequencies
removeLeaf :: Ord t => PQ.PQ Int t -> t -> PQ.PQ Int t
removeLeaf leafFreqs leaf | freq == Nothing = leafFreqs
                          | freq == Just 1  = PQ.delete leaf                     leafFreqs
                          | otherwise       = PQ.update leaf (fromJust freq - 1) leafFreqs
  where freq = leafFreqs `PQ.keyOf` leaf

-- The given set of trees pruned to (restricted to) the given set of leaves
prunedTo :: Ord t => [Tree t] -> S.Set t -> [Tree t]
trees `prunedTo` leaves = map (fromJust . (`restrictedTo` leaves)) trees

-- Basic stats of the generated trees
data Stats = Stats { numInTrees         :: Int  -- The number of input trees
                   , numInLabels        :: Int  -- The total number of labels across all trees
                   , numOutTrees        :: Int  -- The number of output trees
                   , numOutLabels       :: Int  -- The size of the label set of each output tree
                   , numMultifurcations :: Int  -- The number of multifurcations in the output trees
                   , minNodeDegree      :: Int  -- The minimum node degree in the output trees
                   , maxNodeDegree      :: Int  -- The maximum node degree in the output trees
                   , labelSetOk         :: Bool -- Is the label set of the output trees correct
                   , restrictionsOk     :: Bool -- Are the output trees correct restrictions of
                                                -- the selected subset of input trees
                   }
