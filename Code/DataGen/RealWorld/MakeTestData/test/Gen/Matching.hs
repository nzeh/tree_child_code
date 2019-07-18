{-# LANGUAGE FlexibleInstances, StandaloneDeriving, TemplateHaskell, TupleSections #-}

module Gen.Matching ( HasPath(..)
                    , Matching(..)
                    , MatchingInstance(..)
                    , MaximumMatching(..)
                    , Path(..)
                    , RandomState(..)
                    ) where

import           Control.Arrow
import           Control.Monad (replicateM)
import           Data.List (foldl')
import qualified Data.Map as M
import           Data.Maybe (mapMaybe)
import qualified Data.Set as S
import           Data.Tuple (swap)
import           Private.Matching
import           Test.QuickCheck
import           Util (groups)

-- Random matching
newtype Matching = Matching [(Int, Int)]
                 deriving Show

instance Arbitrary Matching where
  arbitrary = do n     <- getPositive <$> arbitrary
                 nodes <- shuffle [1..2*n]
                 return (Matching $ group2 nodes)
  shrink (Matching es) = map Matching (dropOneElement es)

-- Random path
newtype Path = Path [(Int, Int)]
             deriving Show

instance Arbitrary Path where
  arbitrary = do n     <- getPositive <$> arbitrary
                 nodes <- shuffle [1..2*n]
                 return (Path $ sequence2 nodes)
  shrink (Path [])  = []
  shrink (Path [_]) = [Path []]
  shrink (Path es)  = [Path (tail es), Path (init es)]

-- Random search state
newtype RandomState = RandomState (SearchState Int)
                    deriving Show

deriving instance Eq   (SearchState Int)
deriving instance Show (SearchState Int)

instance Arbitrary RandomState where
  arbitrary = do Forest trees                  <- arbitrary
                 let maxdepth                   = maximum $ map depthOf trees
                 depth                         <- choose (0, maxdepth)
                 let (_, _, allParents)         = extractForestState maxdepth trees
                 let (queue, explored, parents) = extractForestState depth    trees
                 let targets                    = extractTargets trees
                 edges                         <- randomEdges    trees
                 return $ RandomState ( SearchState ( S.fromList explored )
                                                    ( S.fromList queue )
                                                    ( S.fromList targets )
                                                    ( M.fromListWith S.union
                                                    $ map (second S.singleton)
                                                    $ edges ++ map swap allParents
                                                    )
                                                    ( M.fromList parents )
                                      )

-- Random Tree
data Tree = Tree Int [Tree]

instance Arbitrary Tree where
  arbitrary = do Positive n <- arbitrary
                 tree       <- genTree n
                 head <$> labelForest [tree]

-- Random forest
newtype Forest = Forest [Tree]

instance Arbitrary Forest where
  arbitrary = do Positive n <- arbitrary
                 trees      <- replicateM n arbitrary
                 Forest <$> labelForest trees

-- Random search state that ensures a path exists or doesn't
data HasPath = HasPath (SearchState Int) Bool
             deriving Show

instance Arbitrary HasPath where
  arbitrary = do Forest trees'           <- arbitrary
                 hasPath                 <- arbitrary
                 trees                   <- ( if hasPath
                                                then createTargets
                                                else return . killTargets
                                            ) trees'
                 let maxdepth             = maximum $ map depthOf trees
                 let (_, _, allParents)   = extractForestState maxdepth trees
                 let (queue, explored, _) = extractForestState 0        trees
                 let targets              = extractTargets trees
                 edges                   <- randomEdges    trees
                 let s = SearchState ( S.fromList explored )
                                     ( S.fromList queue )
                                     ( S.fromList targets )
                                     ( M.fromListWith S.union
                                     $ map (second S.singleton)
                                     $ edges ++ map swap allParents
                                     )
                                     M.empty
                 return (HasPath s hasPath)

-- Random bipartite graph, matching, and a Bool that indicates whether the
-- matching is maximum
data MaximumMatching = MaximumMatching [(Int, Int)] [(Int, Int)] Bool
                     deriving Show

instance Arbitrary MaximumMatching where
  arbitrary = do isMaximum         <- arbitrary
                 (edges, matching) <- if isMaximum
                                        then genMaximumMatching
                                        else genNonMaximumMatching
                 return (MaximumMatching edges matching isMaximum)

  shrink (MaximumMatching es ms isMax) | isMax || null ms = zipWith joinEsAndMs sublistsOfEs (repeat ms)
                                       | otherwise        = zipWith joinEsAndMs (repeat es)  sublistsOfMs
    where sublistsOfEs        = dropOneElementNotIn es ms
          sublistsOfMs        = dropOneElement ms
          joinEsAndMs es' ms' = MaximumMatching es' ms'' isMax
            where ms'' = S.elems $ S.intersection (S.fromList es') (S.fromList ms')

-- Random maximum matching instance with known size of the maximum matching
data MatchingInstance = MatchingInstance [(Int, Int)] Int
                      deriving Show

instance Arbitrary MatchingInstance where
  arbitrary = do (edges, matching) <- genMaximumMatching
                 return $ MatchingInstance edges (length matching)

-- Return the list of all sublists with one element removed
dropOneElement :: Eq t => [t] -> [[t]]
dropOneElement = flip dropOneElementNotIn []

-- Return the list of all sublists with one element removed that is not in the second list
dropOneElementNotIn :: Eq t => [t] -> [t] -> [[t]]
dropOneElementNotIn []     _  = []
dropOneElementNotIn (x:xs) ys | x `elem` ys =      map (x:) (dropOneElementNotIn xs ys)
                              | otherwise   = xs : map (x:) (dropOneElementNotIn xs ys)

-- Convert a list into a list of pairs by grouping consecutive elements
group2 :: [t] -> [(t, t)]
group2 (x:y:xs) = (x,y) : group2 xs
group2 _        = []

-- Convert a list into a list of pairs of consecutive elements
sequence2 :: [t] -> [(t, t)]
sequence2 (x:ys@(y:_)) = (x,y) : sequence2 ys
sequence2 _            = []

-- The depth of a tree
depthOf :: Tree -> Int
depthOf (Tree _ ts) = maximum (0 : map ((+1) . depthOf) ts)

-- Extract the queue, explored vertices, and their parents up to a given depth from a forest
extractForestState :: Int -> [Tree] -> ([Int], [Int], [(Int, Int)])
extractForestState depth trees = (concat queues, concat exploreds, concat parents)
  where (queues, exploreds, parents) = unzip3 $ map (extractTreeState depth) trees

-- Extract the queue, explored vertices, and their parents up to a given depth from a tree
extractTreeState :: Int -> Tree -> ([Int], [Int], [(Int, Int)])
extractTreeState 0 (Tree x _)  = ([x], [x], [])
extractTreeState d (Tree x cs) = (queue, x : explored, parents ++ thisLevel)
  where (queue, explored, parents) = extractForestState (d-1) cs
        thisLevel                  = map (\(Tree y _) -> (y, x)) cs

-- Extract all nodes at odd depths that have no children.  Those are essentially unmatched
-- vertices on the right side.
extractTargets :: [Tree] -> [Int]
extractTargets trees = odd (Tree 0 trees)
  where even (Tree _ ts) = concatMap odd ts
        odd  (Tree x []) = [x]
        odd  (Tree _ ts) = concatMap even ts

-- Generate a list of random edges between consecutive levels of a tree.
randomEdges :: [Tree] -> Gen [(Int, Int)]
randomEdges trees = do let levels     = extractLevels trees
                           levelPairs = group2 levels
                       concat <$> mapM mkEdges levelPairs

-- Extract the levels of a forest
extractLevels :: [Tree] -> [[Int]]
extractLevels = takeWhile (not . null) . foldr collectNodes (repeat [])
  where collectNodes (Tree x cs) (l:ls) = (x:l) : foldr collectNodes ls cs

-- Generate a list of random edges between two pairs of vertex sets
mkEdges :: ([Int], [Int]) -> Gen [(Int, Int)]
mkEdges (xs, ys) = sublistOf [(x, y) | x <- xs, y <- ys]

-- genTree generates a randomly shaped tree of odd height such that every node at even depth
-- has an arbitrary number of children and every node at odd depth has at most one child.
-- n is the number of leaves at the lowest level.  The expected height of the
-- tree is O(lg n) and the expected number of leaves is O(n).
genTree :: Int -> Gen Tree
genTree n = go True (replicate n $ Tree 0 [])
  where go reduce trees = do continue <- arbitrary
                             if continue || reduce || not (null $ tail trees)
                               then reduceTrees reduce trees >>= intersperseNew >>= go (not reduce)
                               else return (head trees)

-- Randomly group the existing trees under new parents if reduce == True.  Otherwise, make each
-- tree the unique child of a new parent.
reduceTrees :: Bool -> [Tree] -> Gen [Tree]
reduceTrees reduce trees = do merge <- map (&& reduce) <$> infiniteListOf (elements $ False : replicate 3 True)
                              let taggedTrees = zip merge trees
                              return (map (Tree 0) $ groupSiblings taggedTrees)
  where groupSiblings []     = []
        groupSiblings (t:ts) = (map snd $ t : ts') : groupSiblings ts''
          where (ts', ts'')  = span fst ts

-- Create a new list of trees by randomly interspersing new singleton trees between the trees
-- in the given list of trees.  The expected number of new trees is (length trees) / 2.
intersperseNew :: [Tree] -> Gen [Tree]
intersperseNew trees = do newTrees <- infiniteListOf (elements $ True : replicate 32 False)
                          return (mkTrees newTrees trees)
  where mkTrees (True  : ns) ts     = (Tree 0 []) : mkTrees ns ts
        mkTrees (False : _)  []     = []
        mkTrees (False : ns) (t:ts) = t : mkTrees ns ts

-- Randomly label the nodes of a forest
labelForest :: [Tree] -> Gen [Tree]
labelForest trees = do let n = forestSize trees
                       labels <- shuffle [1..n]
                       return $ reverse (snd $ foldl' labelTree (labels, []) trees)

-- The size of a tree
treeSize :: Tree -> Int
treeSize (Tree _ cs) = 1 + sum (map treeSize cs)

-- The size of a forest
forestSize :: [Tree] -> Int
forestSize = sum . map treeSize

-- Label the nodes of a tree with a list of labels and collect the resulting tree
labelTree :: ([Int], [Tree]) -> Tree -> ([Int], [Tree])
labelTree (l:labels, trees) (Tree _ cs) = (labels', Tree l (reverse cs') : trees)
  where (labels', cs') = foldl' labelTree (labels, []) cs

-- Make sure that there are no targets (leaves at odd depth) in the forest
killTargets :: [Tree] -> [Tree]
killTargets = mapMaybe (go True)
  where go True  l@(Tree _ []) = Just l
        go False   (Tree _ []) = Nothing
        go even    (Tree x cs) | null cs'  = Nothing
                               | otherwise = Just (Tree x cs')
          where cs' = mapMaybe (go $ not even) cs

-- Make sure there is at least one target (leaf at odd depth) in the forest
createTargets :: [Tree] -> Gen [Tree]
createTargets trees | null targets = createTargets' trees
                    | otherwise    = return trees
  where targets = extractTargets trees

createTargets' :: [Tree] -> Gen [Tree]
createTargets' trees = do let m                     = length (extractTargets trees)
                              n                     = forestSize trees
                          InfiniteList addChild' _ <- arbitrary
                          i                        <- choose (0, m-1)
                          labels'                  <- shuffle [n+1..n+m]
                          let addChild = zipWith (||) addChild' [ j == i | j <- [0..m-1]]
                              labels   = zipWith (\pick lbl -> if pick then lbl else 0) addChild labels'
                          return (addTargets trees labels)

addTargets :: [Tree] -> [Int] -> [Tree]
addTargets trees labels = reverse . fst $ foldl' (go False) ([], labels) trees
  where go odd (ts, ls) (Tree x cs) | odd && null cs = (Tree x cs'            : ts, ls')
                                    | otherwise      = (Tree x (reverse cs'') : ts, ls'')
          where l:ls'        = ls
                cs'          = if l > 0 then [Tree l []] else []
                (cs'', ls'') = foldl' (go $ not odd) ([], ls) cs

-- Generator for a maximum matching
genMaximumMatching :: Gen ([(Int, Int)], [(Int, Int)])
genMaximumMatching = do Positive numComps         <- scale (`div` 10) arbitrary
                        numLeftHeavy              <- choose (0, numComps)
                        let numRightHeavy          = numComps - numLeftHeavy
                        leftHeavies               <- map swap <$> replicateM numLeftHeavy  genRightHeavy
                        rightHeavies              <-              replicateM numRightHeavy genRightHeavy
                        let compSizes              = map (uncurry (+)) (leftHeavies ++ rightHeavies)
                            n                      = sum compSizes
                        labels                    <- shuffle [1..n]
                        let compLabels             = groups compSizes labels
                            leftLabelled           = zipWith labelComp leftHeavies compLabels
                            rightLabelled          = zipWith labelComp rightHeavies
                                                             (drop (length leftHeavies) compLabels)
                        leftCompleted             <- mapM addInnerEdges leftLabelled
                        rightCompleted            <- mapM addInnerEdges rightLabelled
                        let leftMatched            = concatMap extractMatchedSide leftLabelled
                            rightMatched           = concatMap extractMatchedSide rightLabelled
                        outerEdges                <- addOuterEdges rightMatched leftMatched
                        let (innerEdges, matching) = (concat *** concat)
                                                   $ unzip (leftCompleted ++ rightCompleted)
                        return (outerEdges ++ innerEdges, matching)

-- Generator for a non-maximum matching
genNonMaximumMatching :: Gen ([(Int, Int)], [(Int, Int)])
genNonMaximumMatching = do NonNegative numLeft               <- scale (`div` 10) arbitrary
                           NonNegative numRight              <- scale (`div` 10) arbitrary
                           NonNegative numMatched            <- scale (`div` 10) arbitrary
                           Positive    pathLength            <- scale (`div` 10) arbitrary
                           let n = numLeft + numRight + 2 * numMatched + pathLength + 1
                           labels                            <- shuffle [1..n]
                           let [leftLabels, rightLabels, matchedLabels, pathLabels] =
                                 groups [numLeft, numRight, 2 * numMatched, pathLength + 1] labels
                               matching                       = group2  matchedLabels
                               (augmentingPath, pathMatching) = genPath pathLabels
                               (pathLeft, pathRight)          = unzip   augmentingPath
                               (matchLeft, matchRight)        = unzip   matching
                               left                           = S.elems . S.fromList
                                                              $ leftLabels ++ matchLeft  ++ pathLeft
                               right                          = S.elems . S.fromList
                                                              $ rightLabels ++ matchRight ++ pathRight
                           randomEdges                       <- addOuterEdges left right
                           let finalMatching                  = matching ++ pathMatching
                               edges                          = S.elems . S.fromList
                                                              $ matching ++ randomEdges ++ augmentingPath
                           return (edges, finalMatching)

-- Generate the number of vertices on the two sides of a component of the graph
-- with more vertices on the right than on the left
genRightHeavy :: Gen (Int, Int)
genRightHeavy = do Positive left  <- scale (`div` 10) arbitrary
                   Positive extra <- scale (`div` 10) arbitrary
                   return (left, left + extra)

-- Label the vertices in a component using a given list of labels
labelComp :: (Int, Int) -> [Int] -> ([Int], [Int])
labelComp (left, _) labels = splitAt left labels

-- Add matching edges and random unmatched edges between the vertices in each component
addInnerEdges :: ([Int], [Int]) -> Gen ([(Int, Int)], [(Int, Int)])
addInnerEdges (left, right) = do let matching = zip left right
                                 randomEdges <- sublistOf [(x, y) | x <- left, y <- right]
                                 let edges    = S.elems
                                              $ S.union (S.fromList matching) (S.fromList randomEdges)
                                 return (edges, matching)

-- Extract the vertices on the smaller side of a component
extractMatchedSide :: ([Int], [Int]) -> [Int]
extractMatchedSide (left, right) | length left < length right = left
                                 | otherwise                  = right

-- Generate a list of unmatched edges between two lists of vertices
addOuterEdges :: [Int] -> [Int] -> Gen [(Int, Int)]
addOuterEdges left right = sublistOf [(x, y) | x <- left, y <- right]

-- Generate a path of the given length but with every other edge flipped to ensure every edge
-- is listed as (left vertex, right vertex)
genPath :: [Int] -> ([(Int, Int)], [(Int, Int)])
genPath labels = (unmatched ++ matching, matching)
  where path                  = sequence2 labels
        unmatched             = head path : unmatched'
        (matched, unmatched') = unzip (group2 $ tail path)
        matching              = map swap matched
