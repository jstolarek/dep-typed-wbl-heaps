----------------------------------------------------------------------
-- Copyright: 2013, Jan Stolarek, Lodz University of Technology     --
--                                                                  --
-- License: See LICENSE file in root of the repo                    --
-- Repo address: https://github.com/jstolarek/dep-typed-heaps       --
--                                                                  --
-- Basic implementation of leftist heap. No dependent types.        --
----------------------------------------------------------------------

{-# LANGUAGE GADTs #-}
module LeftistHeap where

import Heap

type Rank = Int

data LHeap a where
    Empty :: LHeap a
    LHeap :: Rank -> Priority -> a -> LHeap a -> LHeap a -> LHeap a

instance Heap LHeap where
    empty = Empty

    isEmpty Empty = True
    isEmpty _     = False

    singleton p e = LHeap 1 p e Empty Empty

    merge h     Empty = h
    merge Empty h     = h
    merge h1@(LHeap _ p1 x l1 r1) h2@(LHeap _ p2 y l2 r2)
        | p1 < p2     = makeT p1 x l1 (merge r1 h2)
        | otherwise   = makeT p2 y l2 (merge h1 r2)

    insert p x h = merge (singleton p x) h

    findMin Empty             = error "Empty heap"
    findMin (LHeap _ _ x _ _) = x

    deleteMin Empty             = error "Empty heap"
    deleteMin (LHeap _ _ _ l r) = merge l r

rank :: LHeap a -> Rank
rank Empty           = 0
rank (LHeap r _ _ _ _) = r

makeT :: Priority -> a -> LHeap a -> LHeap a -> LHeap a
makeT p x l r | rank_l >= rank_r = LHeap (rank_r + 1) p x l r
              | otherwise        = LHeap (rank_l + 1) p x r l
              where rank_l = rank l
                    rank_r = rank r
