{-# LANGUAGE FlexibleInstances, StandaloneDeriving, TemplateHaskell, TupleSections #-}

module Test.Matching ( tests
                     ) where

import qualified Data.Map as M
import           Data.Maybe (fromMaybe, isNothing, mapMaybe)
import qualified Data.Set as S
import           Gen.Matching
import           Private.Matching
import           Test.QuickCheck
import           Util (union)

-- Test that complementing the path works
prop_augmentedWithPath (Matching m) (Path p) = classify (S.disjoint mset pset) "trivial"
                                             $ pset  == (S.union m_in_p      m'_in_p) &&
                                               mset  == (S.union m_not_in_p  m_in_p)  &&
                                               m'set == (S.union m'_not_in_p m'_in_p)
  where m'          = m `augmentedWithPath` p
        mset        = S.fromList m
        pset        = S.fromList (directLeftRight p)
        m'set       = S.fromList m'
        m_in_p      = S.intersection mset  pset
        m_not_in_p  = S.difference   mset  pset
        m'_in_p     = S.intersection m'set pset
        m'_not_in_p = S.difference   m'set pset

-- Test that nextState updates the state correctly
prop_nextState (RandomState s) = classify (S.null q)                              "empty in"
                               $ classify (S.null q' && not (S.null q))           "empty out"
                               $ classify (S.null $ S.intersection q hasChildren) "trivial"
                               $ explored s' == expectedExplored &&
                                 queue    s' == expectedQueue    &&
                                 targets  s' == targets s        &&
                                 children s' == children s       &&
                                 existingParentsPreserved        &&
                                 newParentsInOldQueue
  where q  = queue s
        q' = queue s'
        s' = nextState s
        hasChildren              = M.keysSet (children s `M.restrictKeys` q)
        expectedExplored         = S.union (explored s) expectedQueue
        expectedQueue            = S.difference newlyReachable (explored s)
        existingParentsPreserved = parents s `M.isSubmapOf` parents s'
        newParentsInOldQueue     = expectedQueue `S.isSubsetOf` M.keysSet (parents s') &&
                                   S.map (parents s' M.!) expectedQueue `S.isSubsetOf` q
        newlyReachable           = union $ mapMaybe (flip M.lookup $ children s) (S.elems $ queue s)

-- Test that extractPath works
prop_extractPath (RandomState s) = n > 0 ==> isPath && pathExists
  where founds          = S.intersection (targets s) (queue s)
        n               = S.size founds
        path            = extractPath s
        isPath          = and $ zipWith (==) (map snd path) (map fst $ tail path)
        expectedParents = map (Just . fst) path
        realParents     = map (flip M.lookup (parents s) . snd) path
        pathExists      = expectedParents == realParents

-- Check that augmentingPath finds an augmenting path exactly when it should, and it finds
-- the right path
prop_augmentingPath (HasPath s hasPath) = classify hasPath       "path exists"
                                        $ classify (not hasPath) "no path exists"
                                        $ (    hasPath && isPath && pathExists && oddLength) ||
                                          (not hasPath && noPathFound)
  where noPathFound    = isNothing path
        isPath         = maybe False (\p -> and $ zipWith (==) (map snd p) (map fst $ tail p)) path
        pathExists     = maybe False (all isChild) path
        isChild (x, y) = maybe False (y `S.member`) (M.lookup x $ children s)
        oddLength      = fromMaybe False ((odd . length) <$> path)
        path           = augmentingPath s

-- Check that we augment a bipartite matching correctly
prop_augmentBipartiteMatching (MaximumMatching edges matching isMaximum) =
  classify      isMaximum  "maximum matching"                            $
  classify (not isMaximum) "no maximum matching"                         $
  (    isMaximum && isNothing  matching') ||
  (not isMaximum && maybe False (isMatching edges) matching'
                 && newLength == length matching + 1)
  where matching' = augmentBipartiteMatching edges matching
        newLength = maybe 0 length matching'

-- Test whether the given matching is in fact a matching
isMatching :: [(Int, Int)] -> [(Int, Int)] -> Bool
isMatching edges matching = matchedSet `S.isSubsetOf` edgeSet &&
                            S.size leftSet  == length left    &&
                            S.size rightSet == length right
  where (left, right) = unzip matching
        leftSet       = S.fromList left
        rightSet      = S.fromList right
        matchedSet    = S.fromList matching
        edgeSet       = S.fromList edges

-- Test that we correctly find a maximum matching.
prop_bipartiteMaximumMatching (MatchingInstance edges matchSize) =
  classify (matchSize == 0) "trivial"                            $
  classify (matchSize > 50) "large"                              $
  length matching == matchSize && isMatching edges matching
  where matching = bipartiteMaximumMatching edges

return []
tests :: (String, [(String, Property)])
tests = ("Matching", $allProperties)
