-- A simple priority queue implementation using a map and a set.  Quick and dirty.
module PQ ( PQ
          , empty
          , fromList
          , insert
          , update
          , delete
          , deleteMin
          , deleteMax
          , keyOf
          , size
          , isEmpty
          ) where

import Private.PQ
