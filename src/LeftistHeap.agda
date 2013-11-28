----------------------------------------------------------------------
-- Copyright: 2013, Jan Stolarek, Lodz University of Technology     --
--                                                                  --
-- License: See LICENSE file in root of the repo                    --
-- Repo address: https://github.com/jstolarek/dep-typed-heaps       --
--                                                                  --
-- Re-implements basic Haskell implementation of leftist heap.      --
-- No dependent types.                                              --
----------------------------------------------------------------------

module LeftistHeap where

open import Basics
open import Heap

-- TODO; Give definition of rank in a leftist heap
Rank : Set
Rank = Nat

data LHeap (A : Set) : Set where
  lhEmpty : LHeap A
  lhNode  : Rank → Priority → A → LHeap A → LHeap A → LHeap A

rank : {A : Set} → LHeap A -> Nat
rank lhEmpty = zero
rank (lhNode r _ _ _ _) = r

lhIsEmpty : {A : Set} → LHeap A → Bool
lhIsEmpty lhEmpty            = true
lhIsEmpty (lhNode _ _ _ _ _) = false

lhSingleton : {A : Set} → Priority → A → LHeap A
lhSingleton p x = lhNode one p x lhEmpty lhEmpty

makeT : {A : Set} → Priority → A → LHeap A → LHeap A → LHeap A
makeT p x l r with rank l
makeT p x l r | rank_l with rank r
makeT p x l r | rank_l | rank_r with rank_l ≥ rank_r
makeT p x l r | rank_l | rank_r | true  = lhNode (suc rank_r) p x l r
makeT p x l r | rank_l | rank_r | false = lhNode (suc rank_l) p x r l

lhMerge : {A : Set} → LHeap A → LHeap A → LHeap A
lhMerge lhEmpty h₂ = h₂
lhMerge h₁ lhEmpty = h₁
lhMerge (lhNode w1 p1 x1 l1 r1) (lhNode w2 p2 x2 l2 r2) =
  if p1 < p2
  then makeT p1 x1 l1 (lhMerge r1 (lhNode w2 p2 x2 l2 r2))
  else makeT p2 x2 l2 (lhMerge (lhNode w1 p1 x1 l1 r1) r2)

lhInsert : {A : Set} → Priority → A → LHeap A → LHeap A
lhInsert p x h = lhMerge (lhSingleton p x) h

lhFindMin : {A : Set} → LHeap A → A
lhFindMin lhEmpty = {!!} -- can't insert anything here!
lhFindMin (lhNode _ _ x _ _) = x

lhDeleteMin : {A : Set} → LHeap A → LHeap A
lhDeleteMin lhEmpty = {!!} -- can't insert anything here!
lhDeleteMin (lhNode _ _ _ l r) = lhMerge l r

lHeap : Heap \ A → LHeap A
lHeap = record { empty     = lhEmpty;
                 isEmpty   = lhIsEmpty;
                 singleton = lhSingleton;
                 merge     = lhMerge;
                 insert    = lhInsert;
                 findMin   = lhFindMin;
                 deleteMin = lhDeleteMin
               }
