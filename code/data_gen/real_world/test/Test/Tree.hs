{-# LANGUAGE FlexibleInstances, ScopedTypeVariables, StandaloneDeriving, TemplateHaskell #-}

module Test.Tree ( tests
                 ) where

import           Control.Arrow
import           Data.Maybe (fromMaybe, mapMaybe)
import qualified Data.Set as S
import           Gen.Tree
import           Private.Tree
import           Test.QuickCheck
import qualified Util as U

-- Check that binary trees are classified correctly
prop_isBinary tree = classify (n >= 10)           "n >= 10"
                   $ classify (n <  10)           "n < 10"
                   $ classify (      null multis) "binary"
                   $ classify (not $ null multis) "non-binary"
                   $ isBinary tree == null multis
  where _      = tree :: Tree Int
        multis = filter ((> 2) . S.size) (children tree)
        n      = S.size (labelSetOf tree)

-- Check that numberOfMultifurcationsIn counts the number of multifurcations correctly
prop_numberOfMultifurcationsIn tree = classify (n >= 10)            "n >= 10"
                                    $ classify (n <  10)            "n < 10"
                                    $ classify (length multis == 0) "trivial"
                                    $ numberOfMultifurcationsIn tree == length multis
  where _      = tree :: Tree Int
        multis = filter ((> 2) . S.size) (children tree)
        n      = S.size (labelSetOf tree)

-- Check that minmaxNodeDegreesOf counts the minimum and maximum node degrees correctly
prop_minmaxNodeDegreesOf tree = not (null chlds) ==> classify (n >= 10) "n >= 10"
                                                   $ classify (n <  10) "n < 10"
                                                   $ minmaxNodeDegreesOf tree == minmaxdegs
  where _          = tree :: Tree Int
        chlds      = children tree
        minmaxdegs = (minimum &&& maximum) $ map S.size chlds
        n          = S.size (labelSetOf tree)

-- The lists of children of the nodes in the given tree
children :: Tree t -> [S.Set (Tree t)]
children (Leaf _)  = []
children (Node cs) = cs : concatMap children (S.elems cs)

-- Check that the label set of a tree is determined correctly
prop_isLabelSetOf (tree, modify, rands) = classify same    "Same"
                                        $ classify bigger  "Bigger"
                                        $ classify smaller "Smaller"
                                        $ classify random  "Random"
                                        $ (modLabels `isLabelSetOf` tree) == same
  where _         = tree :: Tree Int
        labels    = labelSetOf tree
        modLabels = case modify of
                      Same    -> labels
                      Add     -> S.union      labels (S.fromList rands)
                      Remove  -> S.difference labels (S.fromList rands)
                      Replace ->                      S.fromList rands
        same      = labels == modLabels
        bigger    = not same && labels    `S.isSubsetOf` modLabels
        smaller   = not same && modLabels `S.isSubsetOf` labels
        random    = not (same || bigger || smaller)

-- Check correctness of isRestrictionOf
prop_isRestrictionOf (modify, DisjointTrees tree exts, otherTree, InfiniteList prune _) =
  classify same       "Same"                                                            $
  classify extended   "Extended"                                                        $
  classify restricted "Restricted"                                                      $
  classify random     "Random"                                                          $
  (maybe True (`isRestrictionOf` tree) subtree) == (subclusters == restrictedClusters)
  where _                     = tree :: Tree Int
        subtree               = case modify of
                                  Same    -> Just $                  tree
                                  Remove  ->        pruneTree  prune tree
                                  Add     -> Just $ extendTree exts  tree
                                  Replace -> Just $ otherTree
        sublabels             = maybe S.empty labelSetOf subtree
        subclusters           = maybe S.empty clustersOf subtree
        clusters              = clustersOf tree
        labels                = labelSetOf tree
        restrictedClusters    = S.delete S.empty $ S.map (S.intersection sublabels) clusters
        restrictedSubclusters = S.delete S.empty $ S.map (S.intersection labels)    subclusters
        same                  =             (labels == sublabels)
                                         && (subclusters == restrictedClusters)
        restricted            = not same && (sublabels `S.isSubsetOf` labels)
                                         && (subclusters == restrictedClusters)
        extended              = not same && (labels `S.isSubsetOf` sublabels)
                                         && (clusters == restrictedSubclusters)
        random                = not (same || restricted || extended)

-- Prune a tree to a subset of randomly selected leaves
pruneTree :: [Bool] -> Tree Int -> Maybe (Tree Int)
pruneTree prune tree = tree `restrictedTo` sublabels
  where sublabels = S.fromList $ map fst $ filter snd $ zip (S.elems $ labelSetOf tree) prune

-- Extend a tree with a random selection of additional subtrees per internal node
extendTree :: [[Tree Int]] -> Tree Int -> Tree Int
extendTree exts tree = head . fst $ go ([], exts) tree
  where go (nodes,     exts) l@(Leaf _)  = (                             l : nodes, exts)
        go (nodes, ext:exts)   (Node cs) = (Node (S.fromList $ cs' ++ ext) : nodes, exts')
          where (cs', exts') = foldl go ([], exts) cs

-- Check correctness of clustersOf
prop_clustersOf tree = classify (n <  50) "n < 50"
                     $ classify (n >= 50) "n >= 50"
                     $ clusters == subtreeLabelSets
  where _                = tree :: Tree Int
        clusters         = clustersOf tree
        subtreeLabelSets = lsets tree
        n                = S.size clusters
        lsets t          = S.insert (labelSetOf t) subsets
          where subsets | Leaf _  <- t = S.empty
                        | Node cs <- t = S.foldl' (\ss c -> S.union (lsets c) ss) S.empty cs

-- Check correctness of labelSetOf
prop_labelSetOf tree = classify (n <  50) "n < 50"
                     $ classify (n >= 50) "n >= 50"
                     $ labels == S.fromList [1..n]
  where _      = tree :: Tree Int
        labels = labelSetOf tree
        n      = treeSize tree
        treeSize (Leaf _)  = 1
        treeSize (Node cs) = sum $ map treeSize $ S.elems cs

-- Check that the restriction has the right label set
prop_restrictedTo_labelsSetOf tree (InfiniteList prune _) = classify (subtree == Nothing) "empty"
                                                          $ classify (n > 0 && n < 50)    "n < 50"
                                                          $ classify (n >= 50)            "n >= 50"
                                                          $ restrictedLabels == sublabels
  where _                = tree :: Tree Int
        labels           = labelSetOf tree
        restrictedLabels = S.fromList $ map fst $ filter snd $ zip (S.elems labels) prune
        subtree          = tree `restrictedTo` restrictedLabels
        sublabels        = maybe S.empty labelSetOf subtree
        n                = S.size restrictedLabels

-- Check that the restriction has the right set of clusters
prop_restrictedTo_clustersOf tree (InfiniteList prune _) = classify (subtree == Nothing) "empty"
                                                         $ classify (n > 0 && n < 50)    "n < 50"
                                                         $ classify (n >= 50)            "n >= 50"
                                                         $ restrictedClusters == subclusters
  where _                  = tree :: Tree Int
        labels             = labelSetOf tree
        restrictedLabels   = S.fromList $ map fst $ filter snd $ zip (S.elems labels) prune
        subtree            = tree `restrictedTo` restrictedLabels
        n                  = S.size restrictedLabels
        clusters           = clustersOf tree
        subclusters        = maybe S.empty clustersOf subtree
        restrictedClusters = S.delete S.empty $ S.map (S.intersection restrictedLabels) clusters

-- Check equality of trees
prop_TreeEq tree1 maybeTree2 = classify (tree1 == tree2)  "equal"
                             $ classify (tree1 /= tree2)  "not equal"
                             $ classify (singletons == 1) "one singleton"
                             $ classify (singletons == 2) "two singletons"
                             $ (tree1 == tree2) == (clusters1 == clusters2)
  where _                    = tree1 :: Tree Int
        tree2                = fromMaybe tree1 maybeTree2
        clusters1            = clustersOf tree1
        clusters2            = clustersOf tree2
        singletons           = length $ filter isSingleton [tree1, tree2]
        isSingleton (Leaf _) = True
        isSingleton _        = False

-- Check ordering of trees.  We're only checking basic consistency properties here because
-- anything else boils down to simply re-implementing the Ord instance
prop_TreeEq_implies_TreeLT tree1 maybeTree2 = classify (tree1 == tree2)  "equal"
                                            $ classify (tree1 /= tree2)  "not equal"
                                            $ classify (singletons == 1) "one singleton"
                                            $ classify (singletons == 2) "two singletons"
                                            $ (tree1 == tree2) <= (tree1 <= tree2)
  where _                    = tree1 :: Tree Int
        tree2                = fromMaybe tree1 maybeTree2
        singletons           = length $ filter isSingleton [tree1, tree2]
        isSingleton (Leaf _) = True
        isSingleton _        = False

prop_TreeEq_implies_TreeGT tree1 maybeTree2 = classify (tree1 == tree2)  "equal"
                                            $ classify (tree1 /= tree2)  "not equal"
                                            $ classify (singletons == 1) "one singleton"
                                            $ classify (singletons == 2) "two singletons"
                                            $ (tree1 == tree2) <= (tree1 >= tree2)
  where _                    = tree1 :: Tree Int
        tree2                = fromMaybe tree1 maybeTree2
        singletons           = length $ filter isSingleton [tree1, tree2]
        isSingleton (Leaf _) = True
        isSingleton _        = False

prop_TreeLE_and_TreeGE_implies_TreeEq tree1 maybeTree2 = classify (tree1 == tree2)  "equal"
                                                       $ classify (tree1 /= tree2)  "not equal"
                                                       $ classify (singletons == 1) "one singleton"
                                                       $ classify (singletons == 2) "two singletons"
                                                       $ (tree1 <= tree2 && tree1 >= tree2) <= (tree1 == tree2)
  where _                    = tree1 :: Tree Int
        tree2                = fromMaybe tree1 maybeTree2
        singletons           = length $ filter isSingleton [tree1, tree2]
        isSingleton (Leaf _) = True
        isSingleton _        = False

prop_not_TreeEq_and_TreeLess tree1 maybeTree2 = classify (tree1 == tree2)  "equal"
                                              $ classify (tree1 /= tree2)  "not equal"
                                              $ classify (singletons == 1) "one singleton"
                                              $ classify (singletons == 2) "two singletons"
                                              $ not (tree1 == tree2 && tree1 < tree2)
  where _                    = tree1 :: Tree Int
        tree2                = fromMaybe tree1 maybeTree2
        singletons           = length $ filter isSingleton [tree1, tree2]
        isSingleton (Leaf _) = True
        isSingleton _        = False

prop_not_TreeEq_and_TreeGreater tree1 maybeTree2 = classify (tree1 == tree2)  "equal"
                                                 $ classify (tree1 /= tree2)  "not equal"
                                                 $ classify (singletons == 1) "one singleton"
                                                 $ classify (singletons == 2) "two singletons"
                                                 $ not (tree1 == tree2 && tree1 > tree2)
  where _                    = tree1 :: Tree Int
        tree2                = fromMaybe tree1 maybeTree2
        singletons           = length $ filter isSingleton [tree1, tree2]
        isSingleton (Leaf _) = True
        isSingleton _        = False

prop_not_TreeLE_and_TreeGreater tree1 maybeTree2 = classify (tree1 == tree2)  "equal"
                                                 $ classify (tree1 /= tree2)  "not equal"
                                                 $ classify (singletons == 1) "one singleton"
                                                 $ classify (singletons == 2) "two singletons"
                                                 $ not (tree1 <= tree2 && tree1 > tree2)
  where _                    = tree1 :: Tree Int
        tree2                = fromMaybe tree1 maybeTree2
        singletons           = length $ filter isSingleton [tree1, tree2]
        isSingleton (Leaf _) = True
        isSingleton _        = False

prop_not_TreeGE_and_TreeLess tree1 maybeTree2 = classify (tree1 == tree2)  "equal"
                                              $ classify (tree1 /= tree2)  "not equal"
                                              $ classify (singletons == 1) "one singleton"
                                              $ classify (singletons == 2) "two singletons"
                                              $ not (tree1 >= tree2 && tree1 < tree2)
  where _                    = tree1 :: Tree Int
        tree2                = fromMaybe tree1 maybeTree2
        singletons           = length $ filter isSingleton [tree1, tree2]
        isSingleton (Leaf _) = True
        isSingleton _        = False

prop_not_TreeNE_is_TreeLessOrGreater tree1 maybeTree2 = classify (tree1 == tree2)  "equal"
                                                      $ classify (tree1 /= tree2)  "not equal"
                                                      $ classify (singletons == 1) "one singleton"
                                                      $ classify (singletons == 2) "two singletons"
                                                      $ (tree1 /= tree2) == (tree1 < tree2 || tree1 > tree2)
  where _                    = tree1 :: Tree Int
        tree2                = fromMaybe tree1 maybeTree2
        singletons           = length $ filter isSingleton [tree1, tree2]
        isSingleton (Leaf _) = True
        isSingleton _        = False

prop_not_TreeLE_matches_TreeGE tree1 maybeTree2 = classify (tree1 == tree2)  "equal"
                                                $ classify (tree1 /= tree2)  "not equal"
                                                $ classify (singletons == 1) "one singleton"
                                                $ classify (singletons == 2) "two singletons"
                                                $ (tree1 <= tree2) == (tree2 >= tree1)
  where _                    = tree1 :: Tree Int
        tree2                = fromMaybe tree1 maybeTree2
        singletons           = length $ filter isSingleton [tree1, tree2]
        isSingleton (Leaf _) = True
        isSingleton _        = False

prop_not_TreeLess_matches_TreeGreater tree1 maybeTree2 = classify (tree1 == tree2)  "equal"
                                                       $ classify (tree1 /= tree2)  "not equal"
                                                       $ classify (singletons == 1) "one singleton"
                                                       $ classify (singletons == 2) "two singletons"
                                                       $ (tree1 < tree2) == (tree2 > tree1)
  where _                    = tree1 :: Tree Int
        tree2                = fromMaybe tree1 maybeTree2
        singletons           = length $ filter isSingleton [tree1, tree2]
        isSingleton (Leaf _) = True
        isSingleton _        = False

prop_TreeLE_transitive tree1 tree2 tree3 = classify (tree1 <= tree2 && tree2 <= tree3) "transitive"
                                         $ classify (tree1 >  tree2 && tree2 >  tree3) "reverse transitive"
                                         $ classify (tree1 >  tree2 && tree2 <= tree3) "left failure"
                                         $ classify (tree1 <= tree2 && tree2 >  tree3) "right failure"
                                         $ (tree1 <= tree2 && tree2 <= tree3) <= (tree1 <= tree3)
  where _ = tree1 :: Tree Int

prop_TreeLess_transitive tree1 tree2 tree3 = classify (tree1 <  tree2 && tree2 <  tree3) "transitive"
                                           $ classify (tree1 >= tree2 && tree2 >= tree3) "reverse transitive"
                                           $ classify (tree1 >= tree2 && tree2 <  tree3) "left failure"
                                           $ classify (tree1 <  tree2 && tree2 >= tree3) "right failure"
                                           $ (tree1 < tree2 && tree2 < tree3) <= (tree1 < tree3)
  where _ = tree1 :: Tree Int

-- Test that resolutions are determined correctly.  We only test invariants because anything else
-- becomes re-implementing the definition of the function

-- If both trees are resolutions of each other, they are the same
prop_bidir_isResolutionOf_is_Eq modify tree1 tree2 (InfiniteList rands _) =
  classify (modify == Same)              "same tree"                      $
  classify (modify `elem` [Add, Remove]) "resolution"                     $
  classify (modify == Replace)           "distinct trees"                 $
  ((tree1 `isResolutionOf` tree2') && (tree2' `isResolutionOf` tree1)) <= (tree1 == tree2')
  where _      = tree1 :: Tree Int
        tree2' = case modify of
                   Same    -> tree1
                   -- Since the relation we're testing is symmetric, we can treat addition and
                   -- removal the same
                   Add     -> contract tree1 rands
                   Remove  -> contract tree1 rands
                   Replace -> tree2

-- different label sets means neither resolves the other
prop_isResolutionOf_implies_same_labelSet modify tree1 tree2 (InfiniteList rands _) =
  classify (labelSet1 == labelSet2) "same label set"                                $
  classify (labelSet1 /= labelSet2) "different label sets"                          $
  (tree1' `isResolutionOf` tree2') <= (labelSet1 == labelSet2)
  where _         = tree1 :: Tree Int
        tree1'    = case modify of
                      Add -> contract tree2 rands
                      _   -> tree1
        tree2'    = case modify of
                      Same   -> tree1
                      Remove -> contract tree1 rands
                      _      -> tree2
        labelSet1 = labelSetOf tree1'
        labelSet2 = labelSetOf tree2'

-- Contract some nodes of a tree into their parents
contract :: Ord t => Tree t -> [Bool] -> Tree t
contract tree rands = join . fst $ go tree ([], rands)
  where join [x] = x
        join xs  = Node (S.fromList xs)
        go l@(Leaf _)  (xs,   rands)             = (l:xs, rands)
        go   (Node cs) (xs, r:rands) | r         = (Node (S.fromList xs') : xs,   rands')
                                     | otherwise = (                        xs'', rands'')
          where (xs',  rands')  = foldr go ([], rands) cs
                (xs'', rands'') = foldr go (xs, rands) cs

-- Make sure countMatchingTriplets counts triplets correctly
prop_countMatchingTriplets (CountMatchingTriplets trees siblings) = classify (expectedCount == 0) "trivial"
                                                                  $ expectedCount == computedCount
  where (computedCount, _)       = countMatchingTriplets trees siblings
        expectedCount            = sum $ map numMatchingTriplets trees
        Node cs:sibs             = siblings
        [a,b]                    = S.elems cs
        numMatchingTriplets tree = S.size matchingTriplets
          where matchingTriplets = S.intersection restrictedTriplets (tripletsOf tree)
        restrictedTriplets       = S.fromList $ map mkTriplet [(a, b, c) | a <- aLeaves, b <- bLeaves, c <- cLeaves]
        aLeaves                  = S.elems (labelSetOf a)
        bLeaves                  = S.elems (labelSetOf b)
        cLeaves                  = concatMap (S.elems . labelSetOf) sibs

-- The set of triplets of a tree (includes only resolved triplets)
tripletsOf :: Tree Int -> S.Set (Tree Int)
tripletsOf tree = S.fromList $ filter isResolved triplets
  where leafTriples          = map S.fromList $ S.elems (labelSetOf tree) `U.choose` 3
        triplets             = mapMaybe (tree `restrictedTo`) leafTriples
        isResolved (Node cs) = S.size cs == 2

-- Turn a pair of a 2-element list and an element into a triplet
mkTriplet :: (Int, Int, Int) -> Tree Int
mkTriplet (a, b, c) = Node (S.fromList [Node (S.fromList [Leaf a, Leaf b]), Leaf c])

-- resolutions generates length - 1 resolutions
prop_resolutions_number_of_resolutions (Resolution trees) = classify (length trees < 3) "trivial"
                                                          $ length trees < 3 || length rs == n * (n - 1) `div` 2
  where rs = resolutions trees
        n  = length trees

-- The first tree in every list produced by resolutions has a binary root
prop_resolutions_binary_first_root (Resolution trees) = classify (length trees < 3) "trivial"
                                                      $ all firstRootIsBinary rs
  where rs                            = resolutions trees
        firstRootIsBinary (Node cs:_) = S.size cs == 2
        firstRootIsBinary _           = False

-- resolutions produces resolutions
prop_resolutions_all_resolutions (Resolution trees) = classify (length trees < 3) "trivial"
                                                    $ all isResolution rs
  where rs                        = resolutions trees
        isResolution (Node cs:ts) = S.union cs (S.fromList ts) == treeSet
        isResolution _            = False
        treeSet                   = S.fromList trees

-- resolutions does not produce the same resolution twice
prop_resolutions_no_duplicates (Resolution trees) = classify (length trees < 3) "trivial"
                                                  $ S.size rsSet == n * (n - 1) `div` 2
  where rs    = resolutions trees
        rsSet = S.fromList rs
        n     = length trees

-- resolveMultifurcationsIn produces a resolution of the tree
prop_resolveMultifurcationsIn_resolves_first_tree (Forest trees) forceResolution = classify (length trees < 2) "trivial"
                                                                                 $ length trees < 2 ||
                                                                                   t' `isResolutionOf` t
  where t:ts    = trees
        (_, t') = resolveMultifurcationsIn forceResolution ts t

-- resolveMultifurcationsIn reports whether the tree was changed
prop_resolveMultifurcationsIn_reports_changed_tree (Forest trees) forceResolution =
  classify      trivial                   "trivial"                               $
  classify (not trivial &&     isChanged) "tree was changed"                      $
  classify (not trivial && not isChanged) "tree was not changed"                  $
  isChanged == (t /= t')
  where t:ts            = trees
        (isChanged, t') = resolveMultifurcationsIn forceResolution ts t
        trivial         = length trees < 2

-- resolveMultifurcationsIn performs at most one resolution if forceResolution is False
prop_resolveMultifurcationsIn_force_at_most_one_resolution tree  =
  classify (    isChanged) "tree was changed"     $
  classify (not isChanged) "tree was not changed" $
  atMostOneResolution
  where _                   = tree :: Tree Int
        (isChanged, tree')  = resolveMultifurcationsIn True [tree] tree
        atMostOneResolution = noResolution || oneResolution
        noResolution        = not isChanged && tree == tree'
        oneResolution       =     isChanged && tree' `isResolutionOf` tree &&
                                  S.size (clustersOf tree') == S.size (clustersOf tree) + 1

-- resolveMultifuracitons produces proper resolutions
prop_resolveMultifurcations_resolves_trees (Forest trees) forceResolution =
  classify (length trees < 2) "trivial"                                   $
  length trees < 2 || and (zipWith isResolutionOf trees' trees)
  where (_, trees') = resolveMultifurcations forceResolution trees

-- resolveMultifuracitons returns True if at least one trees is changed
prop_resolveMultifurcations_reports_changed_trees (Forest trees) forceResolution =
  classify      trivial                   "trivial"                              $
  classify (not trivial &&     isChanged) "tree was changed"                     $
  classify (not trivial && not isChanged) "tree was not changed"                 $
  isChanged == or (zipWith (/=) trees' trees)
  where (isChanged, trees') = resolveMultifurcations forceResolution trees
        trivial             = length trees < 2

-- resolveMultifurcations performs exactly one resolution when forceResolution is set
prop_resolveMultifurcations_force_at_most_one_resolution tree =
  classify (    isChanged) "tree was changed"     $
  classify (not isChanged) "tree was not changed" $
  atMostOneResolution
  where _                   = tree :: Tree Int
        trees               = [tree, tree]
        (isChanged, trees') = resolveMultifurcations True trees
        atMostOneResolution = noResolution || oneResolution
        noResolution        = not isChanged && trees' == trees
        oneResolution       =     isChanged && numberOfChangedOnce == 1
        numberOfChangedOnce = length $ filter oneChange $ zip trees trees'
        oneChange (t, t')   = t' `isResolutionOf` t && S.size (clustersOf t') == S.size (clustersOf t) + 1

-- binaryResolutionsOf produces binary resolutions
prop_binaryResolutionsOf (Forest trees) = classify trivial "trivial"        
                                        $ all (uncurry isBinaryResolutionOf) (zip trees' trees)
  where trees'  = binaryResolutionsOf trees
        trivial = length trees < 2 || all isBinary trees

return []
tests :: (String, [(String, Property)])
tests = ("Tree", $allProperties)
