----------------------------------------------------------------------
-- Copyright: 2013, Jan Stolarek, Lodz University of Technology     --
--                                                                  --
-- License: See LICENSE file in root of the repo                    --
-- Repo address: https://github.com/jstolarek/dep-typed-wbl-heaps   --
--                                                                  --
-- Re-implements basic Haskell implementation of weight-biased      --
-- leftist heap. No dependent types.                                --
----------------------------------------------------------------------

module NoProofsNoMakeT where

open import Basics.Nat
open import Basics hiding (_≥_)

-- TODO; Define what is rank in a weight-biased leftist heap
Rank : Set
Rank = Nat

Priority : Set
Priority = Nat

data Heap (A : Set) : Set where
  empty : Heap A
  node  : Rank → Priority → A → Heap A → Heap A → Heap A

rank : {A : Set} → Heap A → Nat
rank empty            = zero
rank (node r _ _ _ _) = r

isEmpty : {A : Set} → Heap A → Bool
isEmpty empty            = true
isEmpty (node _ _ _ _ _) = false

singleton : {A : Set} → Priority → A → Heap A
singleton p x = node one p x empty empty

makeT : {A : Set} → Priority → A → Heap A → Heap A → Heap A
makeT p x l r with rank l | rank r
makeT p x l r | rank_l | rank_r with rank_l ≥ rank_r
makeT p x l r | rank_l | rank_r | true  = node (suc (rank_l + rank_r)) p x l r
makeT p x l r | rank_l | rank_r | false = node (suc (rank_l + rank_r)) p x r l

merge : {A : Set} → Heap A → Heap A → Heap A
merge h1 h2 with h1 | h2
merge h1 h2 | empty | _ = h1
merge h1 h2 | _ | empty = h2
merge h1 h2
  | (node w1 p1 x1 l1 r1)
  | (node w2 p2 x2 l2 r2)
  with p1 < p2
  | rank l1 ≥ rank r1 + rank h2
  | rank l2 ≥ rank r2 + rank h1
merge h1 h2
  | (node w1 p1 x1 l1 r1)
  | (node w2 p2 x2 l2 r2)
  | true
  | true
  | _
  = node (suc (rank h1 + rank h2)) p1 x1 l1 (merge r1 h2)
merge h1 h2
  | (node w1 p1 x1 l1 r1)
  | (node w2 p2 x2 l2 r2)
  | true
  | false
  | _
  = node (suc (rank h1 + rank h2)) p1 x1 (merge r1 h2) l1
merge h1 h2
  | (node w1 p1 x1 l1 r1)
  | (node w2 p2 x2 l2 r2)
  | false
  | _
  | true
  = node (suc (rank h1 + rank h2)) p2 x2 l2 (merge r2 h1)
merge h1 h2
  | (node w1 p1 x1 l1 r1)
  | (node w2 p2 x2 l2 r2)
  | false
  | _
  | false
  = node (suc (rank h1 + rank h2)) p2 x2 (merge r2 h1) l2

insert : {A : Set} → Priority → A → Heap A → Heap A
insert p x h = merge (singleton p x) h

findMin : {A : Set} → Heap A → A
findMin empty = {!!} -- can't insert anything here!
findMin (node _ _ x _ _) = x

deleteMin : {A : Set} → Heap A → Heap A
deleteMin empty = {!!} -- can't insert anything here!
deleteMin (node _ _ _ l r) = merge l r

{-
Heap : Heap \ A → Heap A
Heap = record {
                 empty     = empty;
                 isEmpty   = IsEmpty;
                 singleton = Singleton;
                 merge     = Merge;
                 insert    = Insert;
                 findMin   = FindMin;
                 deleteMin = DeleteMin
               }
-}
