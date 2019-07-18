-- A simple priority queue implementation using a map and a set.  Quick and dirty.

module Private.PQ where

import qualified Data.Map.Strict as M
import qualified Data.Set as S
import           Data.Tuple (swap)

-- The priority queue type
data PQ k v = PQ (M.Map v k) (S.Set (k, v))

-- An empty priority queue
empty :: PQ k v
empty = PQ M.empty S.empty

-- A priority queue containing the elements in the given list
fromList :: (Ord k, Ord v) => [(v, k)] -> PQ k v
fromList elements = PQ (M.fromList elements) (S.fromList $ map swap elements)

-- The priority queue obtained by inserting the given element
insert :: (Ord k, Ord v) => v -> k -> PQ k v -> PQ k v
insert v k (PQ prios ord) = PQ prios' ord'
  where prios' = M.insert v k    prios
        ord'   = S.insert (k, v) ord

-- Replace the priority of the given element with a new priority
update :: (Ord k, Ord v) => v -> k -> PQ k v -> PQ k v
update v k pq@(PQ prios ord) = PQ prios' ord'
  where ord'   = S.insert (k, v) $ maybe ord (\k' -> S.delete (k', v) ord) (pq `keyOf` v)
        prios' = M.insert v k prios

-- The priority queue obtained by deleting the given element
delete :: (Ord k, Ord v) => v -> PQ k v -> PQ k v
delete v pq@(PQ prios ord) = PQ prios' ord'
  where prios' = M.delete v      prios
        ord'   = maybe ord (\k -> S.delete (k, v) ord) (pq `keyOf` v)

-- The minimum element and the priority queue obtained by deleting the minimum element
deleteMin :: Ord v => PQ k v -> ((v, k), PQ k v)
deleteMin (PQ prios ord) = ((v, k), PQ prios' ord')
  where ((k, v), ord') = S.deleteFindMin ord
        prios'         = M.delete v      prios

-- The maximum element and the priority queue obtained by deleting the maximum element
deleteMax :: Ord v => PQ k v -> ((v, k), PQ k v)
deleteMax (PQ prios ord) = ((v, k), PQ prios' ord')
  where ((k, v), ord') = S.deleteFindMax ord
        prios'         = M.delete v      prios

-- Retrieve the key of the given element
keyOf :: Ord v => PQ k v -> v -> Maybe k
keyOf (PQ prios _) v = M.lookup v prios

-- The size of the priority queue
size :: PQ k v -> Int
size (PQ prios _) = M.size prios

-- Is the priority queue empty?
isEmpty :: PQ k v -> Bool
isEmpty (PQ prios _) = M.null prios
