----------------------------------------------------------------------
-- Copyright: 2013, Jan Stolarek, Lodz University of Technology     --
--                                                                  --
-- License: See LICENSE file in root of the repo                    --
-- Repo address: https://github.com/jstolarek/dep-typed-heaps       --
--                                                                  --
-- Dependently-typed implementation of weight-biased leftist heap.  --
-- Work in progress.                                                --
----------------------------------------------------------------------

module DepTypedWeightedHeap where

open import DepTypedBasics

--for the moment we re-invent definition of Heap. This is temporary (I hope)
record Heap (H : Set → Set) : Set1 where
  field
    empty   : ∀ {A} → H A
    isEmpty : ∀ {A} → H A → Bool

    singleton : ∀ {A} → A → H A
    merge  : ∀ {A} → H A → H A → H A
    insert : ∀ {A} → Nat → A → H A → H A

    findMin   : ∀ {A} → H A → A
    deleteMin : ∀ {A} → H A → H A
open Heap {{...}} public

-- TODO: Import Priority from Heap

Priority : Set
Priority = Nat

-- index = tree size
-- TODO: currently there is no proof that priority of node is smaller than
-- its children. Add additional index?
data WBLHeap (A : Set) : Nat → Set where
  wblhEmpty : WBLHeap A zero
  wblhNode  : {l r : Nat} → l ≥ r → Priority → A → WBLHeap A l → WBLHeap A r → WBLHeap A (suc (l + r))

-- Now we have dependent types, so we don't need rank but we need
-- evidence that left rank is at least as large as the right one

wblhIsEmpty : {A : Set} {n : Nat} → WBLHeap A n → Bool
wblhIsEmpty wblhEmpty            = true
wblhIsEmpty (wblhNode _ _ _ _ _) = false

wblhSingleton : {A : Set} → Priority → A → WBLHeap A (suc zero)
wblhSingleton p x = wblhNode ge0 p x wblhEmpty wblhEmpty

-- TODO: unused. Remove? does this function allow me to make the proofs shorter?
wblhMakeT : {A : Set} {l r : Nat} → Priority → A → WBLHeap A l → WBLHeap A r → WBLHeap A (suc (l + r))
wblhMakeT {A} {l-rank} {r-rank} p x l r with order l-rank r-rank
wblhMakeT {A} {l-rank} {r-rank} p x l r | ge lger
  = wblhNode lger p x l r
wblhMakeT {A} {l-rank} {r-rank} p x l r | le rgel
  = subst (WBLHeap A) (cong suc (+comm r-rank l-rank)) (wblhNode rgel p x r l)

-- TODO: rewrite the code so the termination checker does not complain
-- TODO: place proofs in this file, each proof a separate function(s) with comments
wblhMerge : {A : Set} {l r : Nat} → WBLHeap A l → WBLHeap A r → WBLHeap A (l + r)
wblhMerge {A} {zero}  {_}    wblhEmpty h = h
wblhMerge {A} {suc l} {zero} h wblhEmpty =  subst (WBLHeap A) (sym (+0 (suc l))) h
wblhMerge {A} {suc .(l1-rank + r1-rank)} {suc .(l2-rank + r2-rank)}
          (wblhNode {l1-rank} {r1-rank} l1ger1 p1 x1 l1 r1)
          (wblhNode {l2-rank} {r2-rank} l2ger2 p2 x2 l2 r2)
          with p1 < p2
wblhMerge {A} {suc .(l1-rank + r1-rank)} {suc .(l2-rank + r2-rank)}
          (wblhNode {l1-rank} {r1-rank} l1ger1 p1 x1 l1 r1)
          (wblhNode {l2-rank} {r2-rank} l2ger2 p2 x2 l2 r2)
          | true
          with order l1-rank (r1-rank + suc (l2-rank + r2-rank))
wblhMerge {A} {suc .(l1-rank + r1-rank)} {suc .(l2-rank + r2-rank)}
          (wblhNode {l1-rank} {r1-rank} l1ger1 p1 x1 l1 r1)
          (wblhNode {l2-rank} {r2-rank} l2ger2 p2 x2 l2 r2)
          | true
          | ge x -- TODO: rename x
          = subst (WBLHeap A)
                  (cong suc (sym (+assoc l1-rank r1-rank (suc (l2-rank + r2-rank)))))
                  (wblhNode x p1 x1 l1 (wblhMerge r1 (wblhNode l2ger2 p2 x2 l2 r2)))
wblhMerge {A} {suc .(l1-rank + r1-rank)} {suc .(l2-rank + r2-rank)}
          (wblhNode {l1-rank} {r1-rank} l1ger1 p1 x1 l1 r1)
          (wblhNode {l2-rank} {r2-rank} l2ger2 p2 x2 l2 r2)
          | true
          | le x  -- TODO: rename x
          = subst (WBLHeap A)
                  (cong suc (+ac l1-rank r1-rank (suc (l2-rank + r2-rank))))
                  (wblhNode x p1 x1 (wblhMerge r1 (wblhNode l2ger2 p2 x2 l2 r2)) l1)
wblhMerge {A} {suc .(l1-rank + r1-rank)} {suc .(l2-rank + r2-rank)}
          (wblhNode {l1-rank} {r1-rank} l1ger1 p1 x1 l1 r1)
          (wblhNode {l2-rank} {r2-rank} l2ger2 p2 x2 l2 r2)
          | false
          with order l2-rank (r2-rank + suc (l1-rank + r1-rank))
wblhMerge {A} {suc .(l1-rank + r1-rank)} {suc .(l2-rank + r2-rank)}
          (wblhNode {l1-rank} {r1-rank} l1ger1 p1 x1 l1 r1)
          (wblhNode {l2-rank} {r2-rank} l2ger2 p2 x2 l2 r2)
          | false
          | ge x -- TODO: rename x
          = subst (WBLHeap A)
                  (cong suc (+case3 l2-rank r2-rank (l1-rank + r1-rank)))
                  (wblhNode x p2 x2 l2 (wblhMerge r2 (wblhNode l1ger1 p1 x1 l1 r1)))
wblhMerge {A} {suc .(l1-rank + r1-rank)} {suc .(l2-rank + r2-rank)}
          (wblhNode {l1-rank} {r1-rank} l1ger1 p1 x1 l1 r1)
          (wblhNode {l2-rank} {r2-rank} l2ger2 p2 x2 l2 r2)
          | false
          | le x -- TODO: rename x
          = subst (WBLHeap A)
                  (cong suc (+case4 r2-rank (l1-rank + r1-rank) l2-rank) )
                  (wblhNode x p2 x2 ((wblhMerge r2 (wblhNode l1ger1 p1 x1 l1 r1))) l2)

wblhInsert : {A : Set} {n : Nat} → Priority → A → WBLHeap A n → WBLHeap A (suc n)
wblhInsert p x h = wblhMerge (wblhSingleton p x) h

wblhFindMin : {A : Set} {n : Nat} → WBLHeap A (suc n) → A
wblhFindMin (wblhNode _ _ x _ _) = x

wblhDeleteMin : {A : Set} {n : Nat} → WBLHeap A (suc n) → WBLHeap A n
wblhDeleteMin (wblhNode _ _ _ l r) = wblhMerge l r


{-
-- can't write this instance declaration now :-/
wblheap : ∀ {n} → Heap λ A → WBLHeap A n
wblheap = record { empty     = {!!};
                 isEmpty   = wblhIsEmpty;
                 singleton = {!!} --wblhSingleton
--                 merge     = wblhMerge;
--                 insert    = wblhInsert;
--                 findMin   = wblhFindMin;
--                 deleteMin = wblhDeleteMin
               }

-}
