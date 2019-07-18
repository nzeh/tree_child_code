{-# LANGUAGE TemplateHaskell #-}

module Test.PQ ( tests
               ) where

import qualified Data.Map as M
import           Data.Maybe (isJust, isNothing)
import qualified Data.Set as S
import           Private.PQ
import           Test.QuickCheck

-- empty matches isEmpty
prop_empty_isEmpty = isEmpty empty

-- fromList gives isEmpty iff list is null
prop_isEmpty_if_list_is_empty elems = isEmpty pq == null elems
  where _  = elems :: [(Int, Int)]
        pq = fromList elems

-- never isEmpty after insert
prop_not_isEmpty_after_insert elems val key = classify (      null elems) "initially empty"     $
                                              classify (not $ null elems) "initially non-empty" $
                                              not (isEmpty pq)
  where _  = elems :: [(Int, Int)]
        pq = insert val key (fromList elems)

-- size equals number of entries (fromList with unique entries)
prop_size_equals_number_of_elems elems = classify (S.null items) "empty list" $
                                         size pq == S.size items
  where _     = elems :: [(Int, Int)]
        items = S.fromList (map fst elems)
        pq    = fromList elems

-- keyOf after insert matches inserted key
prop_insert_matches_new_key elems val key = classify (old_key == new_key) "key unchanged" $
                                            classify (old_key /= new_key) "key changed"   $
                                            new_key == Just key
  where _       = elems :: [(Int, Int)]
        pq      = fromList elems
        pq'     = insert val key pq
        old_key = keyOf pq  val
        new_key = keyOf pq' val

-- keyOf after update matches updated key
prop_update_matches_new_key elems val old_key new_key = classify (old_key == new_key) "key unchanged" $
                                                        classify (old_key /= new_key) "key changed"   $
                                                        updated_key == Just new_key
  where _           = elems :: [(Int, Int)]
        pq          = insert val old_key (fromList elems)
        pq'         = update val new_key pq
        updated_key = keyOf pq' val

-- delete makes sure the element is not present
prop_delete_removes_the_element elems val = classify (isNothing old_key) "element not present" $
                                            classify (isJust    old_key) "element present"     $
                                            isNothing new_key
  where _       = elems :: [(Int, Int)]
        pq      = fromList elems
        pq'     = delete val pq
        old_key = keyOf pq  val
        new_key = keyOf pq' val

-- insert does not affect other elements
prop_insert_does_not_affect_other_elements elems val key = classify (null elems') "no other elements" $
                                                           all keyMatches elems'
  where _                = elems :: [(Int, Int)]
        elems'           = M.assocs (M.delete val $ M.fromList elems)
        pq               = insert val key (fromList elems')
        keyMatches (v,k) = keyOf pq v == Just k

-- update does not affect other elements
prop_update_does_not_affect_other_elements elems val old_key new_key = classify (null elems') "no other elements" $
                                                                       all keyMatches elems'
  where _                = elems :: [(Int, Int)]
        elems'           = M.assocs (M.delete val $ M.fromList elems)
        pq               = update val new_key $ insert val old_key $ fromList elems'
        keyMatches (v,k) = keyOf pq v == Just k

-- delete does not affect other elements
prop_delete_does_not_affect_other_elements elems val = classify (null elems'') "no other elements" $
                                                       all keyMatches elems''
  where _                = elems :: [(Int, Int)]
        elems'           = M.assocs (M.fromList elems)
        elems''          = filter (\(v,_) -> v /= val) elems'
        pq               = delete val $ fromList elems'
        keyMatches (v,k) = keyOf pq v == Just k

-- deleteMin returns minimum element
prop_deleteMin_returns_minimum_element elems = classify (null elems) "empty priority queue" $
                                               null elems || (m `elem` elems' && k == min_key)
  where _            = elems :: [(Int, Int)]
        elems'       = M.assocs (M.fromList elems)
        pq           = fromList elems'
        (m@(_,k), _) = deleteMin pq
        min_key      = minimum (map snd elems')

-- deleteMin removes the element
prop_deleteMin_removes_the_element elems = classify (null elems) "empty priority queue" $
                                           null elems || isNothing new_key
  where _            = elems :: [(Int, Int)]
        elems'       = M.assocs (M.fromList elems)
        pq           = fromList elems'
        ((v,_), pq') = deleteMin pq
        new_key      = keyOf pq' v

-- deleteMin does not affect any other element
prop_deleteMin_does_not_affect_other_elements elems = classify      (null elems')                  "empty priority queue" $
                                                      classify (not (null elems') && null elems'') "no other elements"    $
                                                      null elems' || all keyMatches elems''
  where _                = elems :: [(Int, Int)]
        elems'           = M.assocs (M.fromList elems)
        pq               = fromList elems'
        ((v, _), pq')    = deleteMin pq
        elems''          | null elems' = elems'
                         | otherwise   = filter (\(v',_) -> v' /= v) elems'
        keyMatches (v,k) = keyOf pq v == Just k

-- deleteMax returns maximum element
prop_deleteMax_returns_minimum_element elems = classify (null elems) "empty priority queue" $
                                               null elems || (m `elem` elems' && k == max_key)
  where _            = elems :: [(Int, Int)]
        elems'       = M.assocs (M.fromList elems)
        pq           = fromList elems'
        (m@(_,k), _) = deleteMax pq
        max_key      = maximum (map snd elems')

-- deleteMax removes the element
prop_deleteMax_removes_the_element elems = classify (null elems) "empty priority queue" $
                                           null elems || isNothing new_key
  where _            = elems :: [(Int, Int)]
        elems'       = M.assocs (M.fromList elems)
        pq           = fromList elems'
        ((v,_), pq') = deleteMax pq
        new_key      = keyOf pq' v

-- deleteMax does not affect any other element
prop_deleteMax_does_not_affect_other_elements elems = classify      (null elems')                  "empty priority queue" $
                                                      classify (not (null elems') && null elems'') "no other elements"    $
                                                      null elems' || all keyMatches elems''
  where _                = elems :: [(Int, Int)]
        elems'           = M.assocs (M.fromList elems)
        pq               = fromList elems'
        ((v, _), pq')    = deleteMax pq
        elems''          | null elems' = elems'
                         | otherwise   = filter (\(v',_) -> v' /= v) elems'
        keyMatches (v,k) = keyOf pq v == Just k

return []
tests :: (String, [(String, Property)])
tests = ("PQ", $allProperties)
