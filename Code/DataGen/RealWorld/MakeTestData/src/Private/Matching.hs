module Private.Matching where

import           Control.Arrow
import           Data.List (unfoldr)
import qualified Data.Map as M
import qualified Data.Set as S
import           Data.Tuple (swap)

-- Find a maximum matching of a bipartite graph.  Needed to match children of a tree node
-- to leaves of a resolution tree.  (I can't convince myself that just finding a match for
-- everybody will indeed result in a matching, but we need a matching.)
bipartiteMaximumMatching :: Ord t => [(t, t)] -> [(t, t)]
bipartiteMaximumMatching edges = go []
  where go matching = maybe matching go (augmentBipartiteMatching edges matching)

-- Given a bipartite graph (represented as a list of edges) and a matching in the graph,
-- try to find a bigger matching.  If the matching is maximum, Nothing is returned.  Otherwise,
-- Just the bigger matching is returned.
augmentBipartiteMatching :: Ord t => [(t, t)] -> [(t, t)] -> Maybe [(t, t)]
augmentBipartiteMatching edges matching = fmap (matching `augmentedWithPath`)
                                               (augmentingPath initState)
  where (leftV,       rightV)           = (S.fromList *** S.fromList) (unzip edges)
        (leftMatched, rightMatched)     = (S.fromList *** S.fromList) (unzip matching)
        [leftUnmatched, rightUnmatched] = zipWith S.difference [leftV,       rightV]
                                                               [leftMatched, rightMatched]
        unmatchedEdges                  = S.elems $ S.difference (S.fromList edges)
                                                                 (S.fromList matching)
        children                        = M.fromListWith S.union
                                        $ map (second S.singleton)
                                        $ unmatchedEdges ++ map swap matching
        initState                       = SearchState { explored = leftUnmatched
                                                      , queue    = leftUnmatched
                                                      , targets  = rightUnmatched
                                                      , children = children
                                                      , parents  = M.empty
                                                      }

-- Given a matching and an augmenting path, return the matching obtained by flipping all
-- the edges on the augmenting path.
augmentedWithPath :: Ord t => [(t, t)] -> [(t, t)] -> [(t, t)]
augmentedWithPath matching path = S.elems (S.union keep add)
  where mset = S.fromList matching
        pset = S.fromList (directLeftRight path)
        keep = S.difference mset pset
        add  = S.difference pset mset

-- Given a path from a left vertex to a right vertex, direct all its edges from left vertices
-- to right vertices.
directLeftRight :: [(t, t)] -> [(t, t)]
directLeftRight (e:es) = e : map swap leftRightEdges ++ rightLeftEdges
  where (leftRightEdges, rightLeftEdges) = unzip $ unfoldr go es
        go (x:y:xs) = Just ((x,y), xs)
        go _        = Nothing

-- Try to find an augmenting path for a given matching of a bipartite graph.  Returns Nothing
-- if no such path exists (that is, the matching is maximum).  Otherwise, it returns Just
-- an augmenting path.
augmentingPath :: Ord t => SearchState t -> Maybe [(t, t)]
augmentingPath state | outOfOptions = Nothing
                     | foundTarget  = Just (extractPath state)
                     | otherwise    = augmentingPath (nextState state)
  where outOfOptions   =        S.null (queue state)
        foundTarget    = (not . S.null) reachedTargets
        reachedTargets = S.intersection (queue state) (targets state)

-- Extract an augmenting path from the current state.  Precondition: The queue and the set of
-- targets must intersect.
extractPath :: Ord t => SearchState t -> [(t, t)]
extractPath state = go end []
  where end = S.elemAt 0 $ S.intersection (queue state) (targets state)
        go x path = maybe path (\y -> go y ((y, x):path)) (M.lookup x (parents state))

-- Advance the search by one level
nextState :: Ord t => SearchState t -> SearchState t
nextState state = state { explored = nextExplored
                        , queue    = nextQueue
                        , parents  = nextParents
                        }
  where hasChildren      = filter (`M.member` children state) (S.elems $ queue state)
        reachableFrom    = M.fromListWith S.union
                         $ concatMap (\x -> zip (S.elems $ children state M.! x) (repeat $ S.singleton x))
                                     hasChildren
        newReachableFrom = reachableFrom `M.withoutKeys` explored state
        newParents       = M.map (S.elemAt 0) newReachableFrom
        nextQueue        = M.keysSet newParents
        nextExplored     = S.union (explored state) nextQueue
        nextParents      = M.union (parents state) newParents

-- State of a search for an augmenting path in a bipartite graph
data SearchState t = SearchState { explored :: S.Set t           -- The vertices seen so far
                                 , queue    :: S.Set t           -- The current frontier
                                 , targets  :: S.Set t           -- The set of vertices we aim to reach
                                 , children :: M.Map t (S.Set t) -- The lists of potential children of all vertices
                                 , parents  :: M.Map t t         -- The parents of vertices in the forest constructed so far
                                 }
