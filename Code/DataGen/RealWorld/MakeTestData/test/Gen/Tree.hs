{-# LANGUAGE FlexibleInstances, ScopedTypeVariables, StandaloneDeriving, TemplateHaskell #-}

module Gen.Tree ( CountMatchingTriplets(..)
                , DisjointTrees(..)
                , Forest(..)
                , Modify(..)
                , Resolution(..)
                ) where

import           Control.Monad (liftM, replicateM)
import           Data.Maybe (mapMaybe)
import qualified Data.Set as S
import           Newick
import           Private.Tree
import           Test.QuickCheck
import           Util (groups, unfoldM)

-- Display trees in Newick format throughout this module
instance Show (Tree Int) where
  show = asNewick

-- Random tree
instance Arbitrary (Tree Int) where
  arbitrary = arbitrary >>= genTree 1 . getPositive

  shrink tree | S.size labels < 2 = []
              | otherwise         = subtrees
    where labels   = labelSetOf tree
          subtrees = mapMaybe (\l -> tree `restrictedTo` (S.delete l labels)) (S.elems labels)

-- Random forest of trees with the same label set
newtype Forest = Forest [Tree Int]
               deriving Show

instance Arbitrary Forest where
  arbitrary = sized $ \s -> do n    <- choose (1, (s+2) `div` 2)
                               let k = (s+2) `div` n
                               Forest <$> replicateM k (genTree 1 n)

  shrink (Forest [])       = []
  shrink (Forest ts@(t:_)) = prunedForest ++ lessTrees
    where labels       = labelSetOf t
          prunedForest = mapMaybe (liftM Forest . pruneForest ts) (S.elems labels)
          lessTrees    = maybe [] (map Forest) (dropOneElement ts)

-- Random forest but 5 times larger than Forest
newtype LargeForest = LargeForest [Tree Int]
                    deriving Show

instance Arbitrary LargeForest where
  arbitrary = do Forest trees <- scale (* 5) arbitrary
                 return (LargeForest trees)

  shrink (LargeForest trees) = map (\(Forest ts) -> LargeForest ts) (shrink $ Forest trees)

-- Random collection of trees with disjoint label sets
data DisjointTrees = DisjointTrees (Tree Int) [[Tree Int]]
                   deriving Show

instance Arbitrary DisjointTrees where
  arbitrary = sized $ \n -> do tree        <- genTree 1 n
                               sibSizes    <- replicateM n (choose (0,10))
                               let numTrees = sum sibSizes
                               trees       <- groups sibSizes <$> unfoldM mkTree (numTrees, n+1)
                               return $ DisjointTrees tree trees
    where mkTree (0, _) = return Nothing
          mkTree (n, x) = do s    <- choose (1,20)
                             tree <- genTree x s
                             return $ Just (tree, (n-1, x+s))

-- Random modification of a tree or forest
data Modify = Same | Add | Remove | Replace
            deriving (Eq, Show)

instance Arbitrary Modify where
  arbitrary = elements [Same, Add, Remove, Replace]

-- Random instance for counting matching triplets
data CountMatchingTriplets = CountMatchingTriplets [Tree Int] [Tree Int]
                           deriving Show

instance Arbitrary CountMatchingTriplets where
  arbitrary = sized $ \s -> do n             <- choose (3, (2*s+6) `div` 2)
                               let k          = (2*s+6) `div` n
                               t:ts          <- replicateM k (genTree 1 n)
                               restrict      <- sublistOfAtLeast 3 (S.elems $ labelSetOf t)
                               restricts     <- map S.fromList <$> randomPartitionOfAtLeast 3 restrict
                               let (a:b:sibs) = mapMaybe (t `restrictedTo`) restricts
                               return (CountMatchingTriplets ts (Node (S.fromList [a,b]):sibs))

-- Random input for generating tree resolutions
newtype Resolution = Resolution [Tree Int]
                   deriving Show

instance Arbitrary Resolution where
  arbitrary = do tree       <- scale (* 10) arbitrary
                 let labels  = S.elems (labelSetOf tree)
                 restricts  <- map S.fromList <$> randomPartition labels
                 let trees   = mapMaybe (tree `restrictedTo`) restricts
                 return (Resolution trees)

-- All induced subtrees with one less leaf
pruneForest :: [Tree Int] -> Int -> Maybe [Tree Int]
pruneForest ts@(t:_) l | null ls   = Nothing
                       | otherwise = Just $ mapMaybe (`restrictedTo` ls) ts
  where ls = S.delete l (labelSetOf t)

-- All sublists with one element removed
dropOneElement :: [t] -> Maybe [[t]]
dropOneElement xs@(_:_) = Just (go xs)
  where go []     = []
        go [_]    = [[]]
        go (x:xs) = xs : map (x:) (go xs)
dropOneElement _ = Nothing

-- Generate a tree with n leaves labelled [x..].  This does all the work in the above tree
-- and forest generators.
genTree :: Int -> Int -> Gen (Tree Int)
genTree x 0 = return (Leaf x)
genTree x 1 = return (Leaf x)
genTree x n = do n'    <- choose (1, n-1)
                 l     <- genTree  x      n'
                 r     <- genTree (x+n') (n-n')
                 multi <- arbitrary
                 let children = case (multi, r) of
                                  (False, _)       -> S.fromList [l, r]
                                  (True,  Leaf _)  -> S.fromList [l, r]
                                  (True,  Node cs) -> S.insert l cs
                 return (Node children)

-- Generator of a sublist of a list containing at least a certain number of elements
sublistOfAtLeast :: Int -> [t] -> Gen [t]
sublistOfAtLeast k xs | n < k     = error $ "Tried to take sublist of length " ++ show k ++ " out of " ++ show n ++ " elements"
                      | otherwise = do pick <- randomBitsAtLeast n k
                                       let tagged = zip pick xs
                                           chosen = filter fst tagged
                                       return (map snd chosen)
  where n = length xs

-- Generate a random bit sequence with at least k True bits in it
randomBitsAtLeast :: Int -> Int -> Gen [Bool]
randomBitsAtLeast n k = go (repeat False)
  where go bits = do newBits <- replicateM n arbitrary
                     let bits'   = zipWith (||) bits newBits
                         setBits = length (filter id bits')
                     if setBits < k
                       then go     bits'
                       else return bits'

-- Generate a random partition of a list into at least k pieces
randomPartitionOfAtLeast :: Int -> [t] -> Gen [[t]]
randomPartitionOfAtLeast k xs | n < k     = error $ "Tried to partition " ++ show n ++ " elements into " ++ show k ++ " groups"
                              | otherwise = do splits <- (++ [False]) <$> randomBitsAtLeast (n-1) (k-1)
                                               return (xs `partitionedAt` splits)
  where n = length xs

-- Partition a list at indices indicated by a Boolean list
partitionedAt :: [t] -> [Bool] -> [[t]]
[]     `partitionedAt` _              = [[]]
(x:xs) `partitionedAt` (split:splits) | split     = [x]   : ps
                                      | otherwise = (x:p) : ps'
  where ps@(p:ps') = xs `partitionedAt` splits

-- Generate a random partition of a list
randomPartition :: [t] -> Gen [[t]]
randomPartition = randomPartitionOfAtLeast 0
