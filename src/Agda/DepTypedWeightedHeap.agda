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

open import Basics

--for the moment we re-invent definition of Heap. This is temporary
record Heap (H : Set → Set) : Set1 where
  field
    empty   : ∀ {A} → H A
    isEmpty : ∀ {A} → H A → Bool

    singleton : ∀ {A} → A → H A
{-
    merge  : ∀ {A} → H A → H A → H A
    insert : ∀ {A} → Nat → A → H A → H A

    findMin   : ∀ {A} → H A → A
    deleteMin : ∀ {A} → H A → H A
-}
open Heap {{...}} public

-- TODO: Move priority to Basics

Priority : Set
Priority = Nat

-- TODO : implement this in haskell and in Agda with no dependent types

-- index = tree size
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
{-

makeT : {A : Set} {l r : Nat} → Priority → A → WBLHeap A l → WBLHeap A r → WBLHeap A (suc (min (order l r)))
makeT {A} {l-rank} {r-rank} p x l r with order l-rank r-rank
makeT p x l r | ge lger = wblhNode lger p x l r
makeT p x l r | le rgel = wblhNode rgel p x r l

-- OK, so it is not true that the resulting heap will have rank l+r. It would be
-- true for weighted heap
wblhMerge : {A : Set} {l r : Nat} → WBLHeap A l → WBLHeap A r → WBLHeap A (l + r)
wblhMerge wblhEmpty h = h
wblhMerge {A} {l} {zero} h wblhEmpty = subst (WBLHeap A) (sym (+0 l)) h -- prove n ≡ n + 0
wblhMerge {A} {suc .r1-rank} {suc .r2-rank}
        (wblhNode {l1-rank} {r1-rank} l1ger1 p1 x1 l1 r1)
        (wblhNode {l2-rank} {r2-rank} l2ger2 p2 x2 l2 r2)
        with order p1 p2
wblhMerge {A} {suc .r1-rank} {suc .r2-rank}
        (wblhNode {l1-rank} {r1-rank} l1ger1 p1 x1 l1 r1)
        (wblhNode {l2-rank} {r2-rank} l2ger2 p2 x2 l2 r2)
        | ge _
        with wblhMerge (wblhNode l1ger1 p1 x1 l1 r1) r2
wblhMerge {A} {suc .r1-rank} {suc .r2-rank}
        (wblhNode {l1-rank} {r1-rank} l1ger1 p1 x1 l1 r1)
        (wblhNode {l2-rank} {r2-rank} l2ger2 p2 x2 l2 r2)
        | ge _
        | wblhNode {lm-rank} {.(r1-rank + r2-rank)} em pm xm lm rm
        with order l2-rank (r1-rank + (suc r2-rank))
wblhMerge {A} {suc .r1-rank} {suc .r2-rank}
        (wblhNode {l1-rank} {r1-rank} l1ger1 p1 x1 l1 r1)
        (wblhNode {l2-rank} {r2-rank} l2ger2 p2 x2 l2 r2)
        | ge _
        | wblhNode {lm-rank} {.(r1-rank + r2-rank)} em pm xm lm rm
        | ge l2≥rm
        = wblhNode l2≥rm p2 x2 l2 (subst (WBLHeap A) (+suc r1-rank r2-rank) (wblhNode em pm xm lm rm))
wblhMerge {A} {suc .r1-rank} {suc .r2-rank}
        (wblhNode {l1-rank} {r1-rank} l1ger1 p1 x1 l1 r1)
        (wblhNode {l2-rank} {r2-rank} l2ger2 p2 x2 l2 r2)
        | ge _
        | wblhNode {lm-rank} {.(r1-rank + r2-rank)} em pm xm lm rm
        | le rm≥l2
        = wblhNode (≥suc (+suc r1-rank r2-rank)) p2 x2 (wblhNode em pm xm lm rm) {!!}
wblhMerge {A} {suc .r1-rank} {suc .r2-rank}
        (wblhNode {l1-rank} {r1-rank} l1ger1 p1 x1 l1 r1)
        (wblhNode {l2-rank} {r2-rank} l2ger2 p2 x2 l2 r2)
        | le x = {!!}

--wblhMerge {A} {suc l} {suc r} (wblhNode l1ger1 p1 x1 l1 r1) (wblhNode l2ger2 p2 x2 l2 r2)
--  | ge x | wblhNode em pm xm lm rm = ?
--  = wblhNode {!!} p2 x2 l2 {!wblhNode em pm xm lm rm!}
--  = makeT p2 x2 l2 (wblhMerge {!wblhNode l1ger1 p1 x1 l1 r1!} r2)
--  = wblhNode {!!} p2 x2 l2 (wblhMerge {!! wblhNode l1ger1 p1 x1 l1 r1 !} r2)
--  = {!!} --makeT p1 x1 l1 (wblhMerge {!l1!} (wblhNode l2ger2 p2 x2 l2 r2))
-}
{-
-- a simple fact - this is wblhNode constructor, we don't need makeT
makeT : {A : Set} {l r : Nat} → l ≥ r → Priority → A → WBLHeap A l → WBLHeap A r → WBLHeap A (suc r)
makeT lger p x l r = wblhNode lger p x l r

-- old version, no proofs
wblhMerge : {A : Set} {n m : Nat} → WBLHeap A n → WBLHeap A m → WBLHeap A (n + m)
wblhMerge wblhEmpty h = h
wblhMerge {A} {n} {zero} h wblhEmpty rewrite rightIdentity n = h -- need to understand this
wblhMerge (wblhNode p1 x1 l1 r1) (wblhNode p2 x2 l2 r2) =
  if p1 < p2
  then makeT p1 x1 l1 (wblhMerge r1 (wblhNode p2 x2 l2 r2))
  else makeT p2 x2 l2 (wblhMerge (wblhNode p1 x1 l1 r1) r2) -- commutativity of addition?

wblhDeleteMin : {A : Set} {n : Nat} → WBLHeap A (suc n) → WBLHeap A ???
wblhDeleteMin wblhEmpty = {!!} -- can't insert anything here!
wblhDeleteMin (wblhNode _ _ _ l r) = wblhMerge l r
-}

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
