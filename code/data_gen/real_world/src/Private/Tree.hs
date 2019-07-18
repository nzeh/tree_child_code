{-# LANGUAGE FlexibleInstances, StandaloneDeriving #-}

module Private.Tree where

import           Control.Arrow
import           Data.Function (on)
import           Data.List (maximumBy)
import           Data.Maybe (catMaybes)
import qualified Data.Set as S
import           Util (partitionK, union)

-- A tree is a labelled leaf or an internal node with a list of trees as its
-- children.
data Tree t = Node !(S.Set (Tree t))
            | Leaf !t

-- Would like to make Tree a functor but cannot quite because the functions
-- that can be used must map from an Ord type to an Ord type
mapTree :: Ord b => (a -> b) -> (Tree a -> Tree b)
mapTree f (Leaf x)  = Leaf (f x)
mapTree f (Node cs) = Node (S.map (mapTree f) cs)

-- Abstract the process of traversing a tree and collecting the information bottom up
foldTree :: (t -> a) -> ([a] -> a) -> (Tree t -> a)
foldTree leafFun nodeFun = go
  where go (Leaf x)  = leafFun x
        go (Node cs) = nodeFun (map go $ S.elems cs)

-- Predicate that tests whether a given tree is binary
isBinary :: Tree t -> Bool
isBinary = foldTree (const True) (\cs -> length cs <= 2 && and cs)

-- Predicate that tests whether a given tree is a resolution of another
isResolutionOf :: Ord t => Tree t -> Tree t -> Bool
tree1 `isResolutionOf` tree2 = (labelSetOf tree1       ==       labelSetOf tree2) &&
                               (clustersOf tree2 `S.isSubsetOf` clustersOf tree1)

-- Predicate that tests whether a given tree is a binary resolution of another
isBinaryResolutionOf :: Ord t => Tree t -> Tree t -> Bool
tree1 `isBinaryResolutionOf` tree2 = (tree1 `isResolutionOf` tree2) && isBinary tree1

-- Count number of multifurcations in a tree
numberOfMultifurcationsIn :: Tree t -> Int
numberOfMultifurcationsIn = foldTree (const 0) (\cs -> sum cs + if length cs > 2 then 1 else 0)

-- Determine the minimum (of internal nodes) and maximum node degree
minmaxNodeDegreesOf :: Tree t -> (Int, Int)
minmaxNodeDegreesOf = foldTree (const (0, 0)) (unzip >>> mindeg *** maxdeg)
  where mindeg = deg >>> minimum
        maxdeg = deg >>> maximum
        deg    = (length &&& id) >>> (uncurry (:)) >>> filter (/= 0)

-- Check that this tree has the given label set
isLabelSetOf :: Ord t => S.Set t -> Tree t -> Bool
labels `isLabelSetOf` tree = labels == labelSetOf tree

-- Check that the first tree is a restriction of the second tree
isRestrictionOf :: Ord t => Tree t -> Tree t -> Bool
subtree `isRestrictionOf` tree = subtreeClusters == restrictedTreeClusters
  where subtreeClusters        = clustersOf subtree
        restrictedTreeClusters = maybe S.empty clustersOf (tree `restrictedTo` labelSetOf subtree)

-- Get the clusters of a given tree
clustersOf :: Ord t => Tree t -> S.Set (S.Set t)
clustersOf = snd . foldTree (S.singleton >>> (id &&& S.singleton)) nodeFun
  where nodeFun = unzip >>> (union *** union) >>> \(c, cs) -> (c, S.insert c cs)

-- The list of leaves of a tree
labelSetOf :: Ord t => Tree t -> S.Set t
labelSetOf = foldTree S.singleton union

-- The restriction of the tree to a given set of leaves
restrictedTo :: Ord t => Tree t -> S.Set t -> Maybe (Tree t)
tree `restrictedTo` leaves = foldTree leafFun nodeFun tree
  where leafFun x  | S.member x leaves = Just (Leaf x)
                   | otherwise         = Nothing
        nodeFun cs | null cs'          = Nothing
                   | [c] <- cs'        = Just c
                   | otherwise         = Just (Node $ S.fromList cs')
          where cs' = catMaybes cs

-- Two trees are equal if they are isomorphic
instance Eq t => Eq (Tree t) where
  (Leaf x)  == (Leaf y)  = x == y
  (Leaf _)  == (Node _)  = False
  (Node _)  == (Leaf _)  = False
  (Node xs) == (Node ys) = xs == ys

-- An ordering on trees.  A leaf is smaller than a non-leaf.  Leaves
-- are compared based on their labels.  Two compound trees are ordered
-- first by the degree of the root and then, left to right by the ordering
-- of their subtrees.
instance Ord t => Ord (Tree t) where
  (Leaf x)  <= (Leaf y)  = x <= y
  (Leaf _)  <= (Node _)  = True
  (Node _)  <= (Leaf _)  = False
  (Node xs) <= (Node ys) = xs <= ys

-- Resolve a collection of multifurcating trees so that the binary resolutions
-- of different trees are as consistent with each other as possible.  Specifically,
-- every multifurcation is resolved so that the set of resolved triplets this creates
-- are in as many trees as possible.
binaryResolutionsOf :: Ord t => [Tree t] -> [Tree t]
binaryResolutionsOf trees | resolved_not_forced = binaryResolutionsOf trees'
                          | resolved_forced     = binaryResolutionsOf trees''
                          | otherwise           = trees
  where (resolved_not_forced, trees')  = resolveMultifurcations False trees
        (resolved_forced,     trees'') = resolveMultifurcations True  trees

-- Resolve all multifurcations that match some refinement in at least one tree
resolveMultifurcations :: Ord t => Bool -> [Tree t] -> (Bool, [Tree t])
resolveMultifurcations forceResolution = go []
  where go _  []                                     = (False,                     [])
        go rs (t:ts) | t_resolved && forceResolution = (t_resolved,                t' : ts)
                     | otherwise                     = (t_resolved || ts_resolved, t' : ts')
          where (t_resolved,  t')  = resolveMultifurcationsIn forceResolution (ts ++ rs) t
                (ts_resolved, ts') = go (t' :  rs) ts

-- Resolve multifurcation(s) in the given tree.  Resolve only the first one
-- found, in a random fashion if forceResolution is True.  Otherwise, resolve
-- as many multifurcations as can be resolved based on at least one newly
-- created triplet being present in the given set of reference trees.  For each
-- multifurcation, pick the resolution that introduces the fewest new triplets.
resolveMultifurcationsIn :: Ord t => Bool -> [Tree t] -> Tree t -> (Bool, Tree t)
resolveMultifurcationsIn forceResolution rs = go
  where go l@(Leaf _)                                     = (False, l)
        go   (Node cs) | numMatches > 0                   = (True,  n'')
                       | forceResolution && S.size cs > 2 = (True,  n')
                       | forceResolution                  = oneChildResolved
                       | otherwise                        = allChildrenResolved
          where (numMatches, cs')   = maximumBy (compare `on` fst)
                                    $ map (countMatchingTriplets rs)
                                    $ resolutions (S.elems cs)
                n'                  = Node (S.fromList cs')
                (_, n'')            = go n'
                childResolutions    = map go (S.elems cs)
                allChildrenResolved = (or   ***  Node . S.fromList) (unzip childResolutions)
                oneChildResolved    = (second $  Node . S.fromList)
                                    $ pickFirstResolvedChild childResolutions (S.elems cs)

        pickFirstResolvedChild []             _                  = (False, [])
        pickFirstResolvedChild ((res, c):crs) (_:cs) | res       = (True,  c:cs)
                                                     | otherwise = (res',  c:cs')
          where (res', cs') = pickFirstResolvedChild crs cs

-- All sets of trees that can be formed by joining two of them under a common root.
-- The first tree in each output list is the one formed by joining two input trees
-- under a common root.
resolutions :: Ord t => [Tree t] -> [[Tree t]]
resolutions trees = map resolve rs
  where rs = trees `partitionK` 2
        resolve (sibs, ts) = Node (S.fromList sibs) : ts

-- Given a list of reference trees and a list of children of a node in a resolution,
-- with the first child being a new binary node, count how many of the new triplets
-- are also triplets of the reference trees, counting multiple occurrences.
countMatchingTriplets :: Ord t => [Tree t] -> [Tree t] -> (Int, [Tree t])
countMatchingTriplets refTrees ts@(Node cs:sibs) | S.size cs /= 2 = (0,                        ts)
                                                 | otherwise      = (sum $ map count refTrees, ts)
  where [a,b]            = S.elems cs
        aLeaves          = labelSetOf a
        bLeaves          = labelSetOf b
        cLeaves          = union (map labelSetOf sibs)
        count            = fst . count'
        count' (Leaf x)  = (0, (mem aLeaves x, mem bLeaves x, mem cLeaves x))
        count' (Node cs) = (numTrips, (numA, numB, numC))
          where numTrips           = numTripsHere + sum subTrips
                [numA, numB, numC] = map sum [subA, subB, subC]
                (subTrips, subABC) = unzip $ map count' (S.elems cs)
                (subA, subB, subC) = unzip3 subABC
                numTripsHere       = sum $ map ctTrips subABC
                ctTrips (a, b, c)  = a * b * (numC - c)
countMatchingTriplets _ ts = (0, ts)

-- A membership indicator for a set and an element
mem :: Ord t => S.Set t -> t -> Int
mem set x | x `S.member` set = 1
          | otherwise        = 0
