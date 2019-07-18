{-# LANGUAGE TemplateHaskell #-}

module Test.Newick ( tests
                   ) where

import Data.Either (isLeft)
import Gen.String
import Gen.Tree
import Private.Newick
import Test.QuickCheck
import Tree

-- Printing a tree and parsing it back is identity
prop_print_and_parse_tree_is_id tree = tree' == Right tree
  where _      = tree :: Tree Int
        newick = asNewick tree
        tree'  = either Left (Right . mapTree read) (treeFromNewick "test" newick)

-- Printing a forest and parsing it back is identity
prop_print_and_parse_forest_is_id (Forest trees) = trees' == Right trees
  where newick = asNewick trees
        trees' = either Left (Right . map (mapTree read)) (treesFromNewick "test" newick)

-- Adding edge lengths to a Newick string does not alter the tree
prop_add_edge_lengths_to_newick_maintains_tree tree (InfiniteList lengths _) = tree' == Right tree
  where _       = tree :: Tree Int
        newick  = asNewick tree
        newick' = addEdgeLengths newick lengths
        tree'   = either Left (Right . mapTree read) (treeFromNewick "test" newick')

-- Adding edge lengths to a multiline Newick string does not alter the forest
prop_add_edge_lengths_to_newick_maintains_forest (Forest trees) (InfiniteList lengths _) =
  trees' == Right trees
  where newick  = asNewick trees
        newick' = addEdgeLengths newick lengths
        trees'  = either Left (Right . map (mapTree read)) (treesFromNewick "test" newick')

-- Adding labels to internal nodes does not alter the tree
prop_add_internal_labels_maintains_tree tree (InfiniteList labels _) = tree' == Right tree
  where _       = tree :: Tree Int
        newick  = asNewick tree
        newick' = addInternalLabels newick labels
        tree'   = either Left (Right . mapTree read) (treeFromNewick "test" newick')

-- Adding labels to internal nodes does not alter the forest
prop_add_internal_labels_maintains_forest (Forest trees) (InfiniteList labels _) = trees' == Right trees
  where newick  = asNewick trees
        newick' = addInternalLabels newick labels
        trees'  = either Left (Right . map (mapTree read)) (treesFromNewick "test" newick')

-- Adding labels and edge lengths does not alter the tree
prop_add_labels_and_edge_lengths_maintains_tree tree (InfiniteList labels _) (InfiniteList lengths _) =
  tree' == Right tree
  where _        = tree :: Tree Int
        newick   = asNewick tree
        newick'  = addEdgeLengths    newick  lengths
        newick'' = addInternalLabels newick' labels
        tree'    = either Left (Right . mapTree read) (treeFromNewick "test" newick'')

-- Adding labels and edge lengths does not alter the forest
prop_add_labels_and_edge_lengths_maintains_forest (Forest trees) (InfiniteList labels _) (InfiniteList lengths _) =
  trees' == Right trees
  where newick   = asNewick trees
        newick'  = addEdgeLengths    newick  lengths
        newick'' = addInternalLabels newick' labels
        trees'    = either Left (Right . map (mapTree read)) (treesFromNewick "test" newick'')

-- Add edge lengths to a given Newick string
addEdgeLengths :: String -> [Maybe Int] -> String
addEdgeLengths "" _              = ""
addEdgeLengths (c:cs) ls@(l:ls') | c `elem` ",);" = maybe cs'' (\l' -> ":" ++ show l' ++ cs'') l
                                 | otherwise      = cs'
  where cs'  = c : addEdgeLengths cs ls
        cs'' = c : addEdgeLengths cs ls'

-- Add internal labels to a given Newick string
addInternalLabels :: String -> [Maybe AlNum] -> String
addInternalLabels ""     _          = ""
addInternalLabels (c:cs) ls@(l:ls') | c == ')'  = c : maybe cs'' (\(AlNum l') -> l' ++ cs'') l
                                    | otherwise = c : cs'
  where cs'  = addInternalLabels cs ls
        cs'' = addInternalLabels cs ls'

-- Reject a one-line string that does not end in a semicolon
prop_reject_missing_semicolon_tree tree = isLeft parseResult
  where _           = tree :: Tree Int
        newick      = init (asNewick tree)
        parseResult = treeFromNewick "test" newick

-- Reject a multi-line string that has at least one line not ending in a semicolon
prop_reject_missing_semicolon_forest (Forest trees) ix = isLeft parseResult
  where newicks             = lines (asNewick trees)
        ix'                 = ix `mod` length newicks
        newicks'            = map dropSemicolon (zip [0..] newicks)
        newick              = unlines newicks'
        parseResult         = treesFromNewick "test" newick
        dropSemicolon (i,l) | i == ix'  = init l
                            | otherwise = l

-- Reject a one-line string with unbalanced parentheses
prop_reject_unbalanced_parentheses_tree tree ix = isLeft parseResult
  where _           = tree :: Tree Int
        newick      = dropParenthesis ix (asNewick tree)
        parseResult = treeFromNewick "test" newick

-- Reject a multi-line string with unbalanced parentheses
prop_reject_unbalanced_parentheses_forest (Forest trees) ix jx = isLeft parseResult
  where newicks              = lines (asNewick trees)
        ix'                  = ix `mod` length newicks
        newicks'             = map dropParenFrom (zip [0..] newicks)
        newick               = unlines newicks'
        parseResult          = treesFromNewick "test" newick
        dropParenFrom (i, l) | i == ix'  = dropParenthesis jx l
                             | otherwise = l

-- Drop a parenthesis from a Newick string (or add one if the string has no parentheses)
dropParenthesis :: Int -> String -> String
dropParenthesis ix newick | numParens == 0 = addParen  (odd ix) newick
                          | otherwise      = dropParen      ix' newick
  where numParens           = length (filter (`elem` "()") newick)
        ix'                 = ix `mod` numParens
        addParen False s    = '(' : s
        addParen True  s    = init s ++ ");"
        dropParen _  ""     = ""
        dropParen ix (c:cs) | ix == 0 && c `elem` "()" =                      cs
                            |            c `elem` "()" = c : dropParen (ix-1) cs
                            | otherwise                = c : dropParen  ix    cs

-- Reject missing comma adjacent to internal node (missing commas between leaves just merge
-- their labels, so won't in general be rejected)
prop_reject_missing_comma_tree tree ix = isLeft parseResult
  where _           = tree :: Tree Int
        newick      = dropComma ix (asNewick tree)
        parseResult = treeFromNewick "test" newick

-- Reject missing comma adjacent to internal node (missing commas between leaves just merge
-- their labels, so won't in general be rejected)
prop_reject_missing_comma_forest (Forest trees) ix = isLeft parseResult
  where newick      = dropComma ix (asNewick trees)
        parseResult = treesFromNewick "test" newick

-- Drop a comma adjacent to a parenthesis if one exists.  Otherwise, splice a subtree "(1,2)"
-- before or after some comma.
dropComma :: Int -> String -> String
dropComma ix newick | length newick < 3 = addC  ix'' newick
                    | numDroppable > 0  = dropC ix'  newick
                    | otherwise         = addC  ix'' newick
  where numSeparators      = length (filter (`elem` ",;") newick)
        numDroppable       = length (filter id $ zipWith isDroppable newick (tail newick))
        isDroppable x succ = x == ',' && succ `elem` "()"
        ix'                = ix `mod` numDroppable
        ix''               = (ix `div` 2) `mod` numSeparators
        addC _  ""         = ""
        addC ix cs@(c:cs') | c `elem` ",;" && ix == 0 = "(1,2)" ++ cs
                           | c `elem` ",;"            = c : addC (ix-1) cs'
                           | otherwise                = c : addC  ix    cs'
        dropC = go ' '
          where go _    _  ""     = ""
                go pred ix (c:cs) | isDroppable && ix == 0 = cs
                                  | isDroppable            = c : go c (ix-1) cs
                                  | otherwise              = c : go c  ix    cs
                  where isDroppable    = c == ',' && succ `elem` "()"
                        succ | null cs   = ' '
                             | otherwise = head cs

-- Reject missing leaf label in a tree
prop_reject_missing_leaf_label_tree tree ix = isLeft parseResult
  where _           = tree :: Tree Int
        newick      = dropLeafLabel ix (asNewick tree)
        parseResult = treeFromNewick "test" newick

-- Reject missing leaf label in a forest
prop_reject_missing_leaf_label_forest (Forest trees) ix = isLeft parseResult
  where newick      = dropLeafLabel ix (asNewick trees)
        parseResult = treesFromNewick "test" newick

-- Drop a leaf label
dropLeafLabel :: Int -> String -> String
dropLeafLabel ix newick = go ix' (zip ('(':newick) newick)
  where numLabels          = length $ filter isLabelStart (zip ('(':newick) newick)
        ix'                = ix `mod` numLabels
        go i (c:cs)        | isLabelStart c && i == 0 = dropWhile (not . (`elem` "():,;")) (map snd cs)
                           | isLabelStart c           = snd c : go (i-1) cs
                           | otherwise                = snd c : go  i    cs
        isLabelStart (p,c) = p `elem` "(," && not (c `elem` "(,")

return []
tests :: (String, [(String, Property)])
tests = ("Newick", $allProperties)
