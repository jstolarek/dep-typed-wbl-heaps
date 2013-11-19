----------------------------------------------------------------------
-- Copyright: 2013, Jan Stolarek, Lodz University of Technology     --
--                                                                  --
-- License: See LICENSE file in root of the repo                    --
-- Repo address: https://github.com/jstolarek/dep-typed-heaps       --
--                                                                  --
-- Re-implements basic Haskell implementation of weight-biased      --
-- leftist heap. No dependent types.                                --
----------------------------------------------------------------------

module WeightedHeap where

open import Basics
open import Heap

-- TODO; Define what is rank in a weight-biased leftist heap
Rank : Set
Rank = Nat

data WBLHeap (A : Set) : Set where
  wblhEmpty : WBLHeap A
  wblhNode  : Rank → Priority → A → WBLHeap A → WBLHeap A → WBLHeap A

rank : {A : Set} → WBLHeap A -> Nat
rank wblhEmpty            = zero
rank (wblhNode r _ _ _ _) = r

wblhIsEmpty : {A : Set} → WBLHeap A → Bool
wblhIsEmpty wblhEmpty            = true
wblhIsEmpty (wblhNode _ _ _ _ _) = false

wblhSingleton : {A : Set} → Priority → A → WBLHeap A
wblhSingleton p x = wblhNode one p x wblhEmpty wblhEmpty

makeT : {A : Set} → Priority → A → WBLHeap A → WBLHeap A → WBLHeap A
makeT p x l r with rank l | rank r
makeT p x l r | rank_l | rank_r with rank_l ≥ rank_r
makeT p x l r | rank_l | rank_r | true  = wblhNode (suc (rank_l + rank_r)) p x l r
makeT p x l r | rank_l | rank_r | false = wblhNode (suc (rank_l + rank_r)) p x r l

wblhMerge : {A : Set} → WBLHeap A → WBLHeap A → WBLHeap A
wblhMerge wblhEmpty h = h
wblhMerge h wblhEmpty = h
wblhMerge (wblhNode w1 p1 x1 l1 r1) (wblhNode w2 p2 x2 l2 r2) =
  if p1 < p2
  then makeT p1 x1 l1 (wblhMerge r1 (wblhNode w2 p2 x2 l2 r2))
  else makeT p2 x2 l2 (wblhMerge (wblhNode w1 p1 x1 l1 r1) r2)

wblhInsert : {A : Set} → Priority → A → WBLHeap A → WBLHeap A
wblhInsert p x h = wblhMerge (wblhSingleton p x) h

wblhFindMin : {A : Set} → WBLHeap A → A
wblhFindMin wblhEmpty = {!!} -- can't insert anything here!
wblhFindMin (wblhNode _ _ x _ _) = x

wblhDeleteMin : {A : Set} → WBLHeap A → WBLHeap A
wblhDeleteMin wblhEmpty = {!!} -- can't insert anything here!
wblhDeleteMin (wblhNode _ _ _ l r) = wblhMerge l r

wblheap : Heap \ A → WBLHeap A
wblheap = record {
                 empty     = wblhEmpty;
                 isEmpty   = wblhIsEmpty;
                 singleton = wblhSingleton;
                 merge     = wblhMerge;
                 insert    = wblhInsert;
                 findMin   = wblhFindMin;
                 deleteMin = wblhDeleteMin
               }
