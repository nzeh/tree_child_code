{-# LANGUAGE TemplateHaskell #-}

module Test.Util ( tests
                 ) where

import           Data.Functor.Identity (runIdentity)
import           Data.List (group, isSubsequenceOf, sort, unfoldr)
import qualified Data.Set as S
import           Private.Util
import           Test.QuickCheck hiding (choose)
import qualified Test.QuickCheck as QC

newtype SmallInt = SmallInt Int

instance Show SmallInt where
  show (SmallInt x) = show x

instance Arbitrary SmallInt where
  arbitrary = SmallInt <$> QC.choose (0, 4)

-- xs `partitionK` k generates (n choose k) sequences
prop_partitionK_length (NonNegative n, SmallInt k) = classify (n < 10)  "n < 10"
                                                   $ classify (n >= 10) "n >= 10"
                                                   $ classify (n < k)   "trivial"
                                                   $ length ps == binom n k
  where xs = [1 .. n]
        ps = xs `partitionK` k

-- Every entry in xs `partitionK` k is a partition of the input
prop_partitionK_is_split (NonNegative n, SmallInt k) = classify (n < 10)  "n < 10"
                                                     $ classify (n >= 10) "n >= 10"
                                                     $ classify (n < k)   "trivial"
                                                     $ all (`isSubsequenceOf` xs) ins  &&
                                                       all (`isSubsequenceOf` xs) outs &&
                                                       all nElems ps
  where xs            = [1 .. n]
        ps            = xs `partitionK` k
        (ins, outs)   = unzip ps
        nElems (i, o) = S.size (S.union (S.fromList i) (S.fromList o)) == n

-- There are no duplicates in xs `choose` k
prop_partitionK_no_dups (NonNegative n, SmallInt k) = classify (n < 10)  "n < 10"
                                                    $ classify (n >= 10) "n >= 10"
                                                    $ classify (n < k)   "trivial"
                                                    $ length ps == length ps'
  where xs = [1 .. n]
        ps = xs `partitionK` k
        ps' = map head $ group $ sort $ ps

-- xs `choose` k generates (n choose k) sequences
prop_choose_length (NonNegative n, SmallInt k) = classify (n < 10)  "n < 10"
                                               $ classify (n >= 10) "n >= 10"
                                               $ classify (n < k)   "trivial"
                                               $ length cs == binom n k
  where xs = [1 .. n]
        cs = xs `choose` k

-- Every sequence in xs `choose` k is a subsequence of xs
prop_choose_subseq (NonNegative n, SmallInt k) = classify (n < 10)  "n < 10"
                                               $ classify (n >= 10) "n >= 10"
                                               $ classify (n < k)   "trivial"
                                               $ all (`isSubsequenceOf` xs) cs
  where xs = [1 .. n]
        cs = xs `choose` k

-- There are no duplicates in xs `choose` k
prop_choose_no_dups (NonNegative n, SmallInt k) = classify (n < 10)  "n < 10"
                                                $ classify (n >= 10) "n >= 10"
                                                $ classify (n < k)   "trivial"
                                                $ length cs == length cs'
  where xs = [1 .. n]
        cs = xs `choose` k
        cs' = map head $ group $ sort $ cs

-- unfoldM over the identity monad is just unfoldr
prop_unfoldM_is_unfoldr n = classify (len < 10)  "n < 10"
                          $ classify (len >= 10) "n >= 10"
                          $ mlist == list
  where mlist = runIdentity $ unfoldM (return . go) 1
        list  = unfoldr go 1
        len   = length list
        go i | i > n     = Nothing
             | otherwise = Just (i, i+1)

-- concatenating and then breaking into groups should be identity
prop_groups_concat_is_id xss = classify (n < 50)  "n < 50"
                             $ classify (n >= 50) "n >= 50"
                             $ xss == xss'
  where xs   = concat xss
        ns   = map length xss
        n    = sum ns
        xss' = groups ns xs

-- binom n k is the binomial coefficient (n choose k)
binom :: Int -> Int -> Int
binom n k | k == 0    = 1
          | k > 0     = binom (n-1) (k-1) * n `div` k
          | otherwise = 0

return []
tests :: (String, [(String, Property)])
tests = ("Util", $allProperties)
