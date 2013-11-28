----------------------------------------------------------------------
-- Copyright: 2013, Jan Stolarek, Lodz University of Technology     --
--                                                                  --
-- License: See LICENSE file in root of the repo                    --
-- Repo address: https://github.com/jstolarek/dep-typed-heaps       --
--                                                                  --
-- Dependently-typed implementation of leftist heap.                --
-- Work in progress.                                                --
----------------------------------------------------------------------

module DepTypedLeftistHeap where

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

Priority : Set
Priority = Nat

-- index = rank (length of right spine)
data LHeap (A : Set) : Nat → Set where
  lhEmpty : LHeap A zero
  lhNode  : {l r : Nat} → l ≥ r → Priority → A → LHeap A l → LHeap A r → LHeap A (suc r)

-- Now we have dependent types, so we don't need rank but we need
-- evidence that left rank is at least as large as the right one

lhIsEmpty : {A : Set} {n : Nat} → LHeap A n → Bool
lhIsEmpty {A} {zero } lhEmpty            = true
lhIsEmpty {A} {suc n} (lhNode _ _ _ _ _) = false

lhSingleton : {A : Set} → Priority → A → LHeap A (suc zero)
lhSingleton p x = lhNode ge0 p x lhEmpty lhEmpty

makeT : {A : Set} {l r : Nat} → Priority → A → LHeap A l → LHeap A r → LHeap A (suc (min (order l r)))
makeT {A} {l-rank} {r-rank} p x l r with order l-rank r-rank
makeT p x l r | ge lger = lhNode lger p x l r
makeT p x l r | le rgel = lhNode rgel p x r l

-- OK, so it is not true that the resulting heap will have rank l+r. It would be
-- true for weighted heap
lhMerge : {A : Set} {l r : Nat} → LHeap A l → LHeap A r → LHeap A (l + r)
lhMerge lhEmpty h = h
lhMerge {A} {l} {zero} h lhEmpty = subst (LHeap A) (sym (+0 l)) h -- prove n ≡ n + 0
lhMerge {A} {suc .r1-rank} {suc .r2-rank}
        (lhNode {l1-rank} {r1-rank} l1ger1 p1 x1 l1 r1)
        (lhNode {l2-rank} {r2-rank} l2ger2 p2 x2 l2 r2)
        with order p1 p2
lhMerge {A} {suc .r1-rank} {suc .r2-rank}
        (lhNode {l1-rank} {r1-rank} l1ger1 p1 x1 l1 r1)
        (lhNode {l2-rank} {r2-rank} l2ger2 p2 x2 l2 r2)
        | ge _
        with lhMerge (lhNode l1ger1 p1 x1 l1 r1) r2
lhMerge {A} {suc .r1-rank} {suc .r2-rank}
        (lhNode {l1-rank} {r1-rank} l1ger1 p1 x1 l1 r1)
        (lhNode {l2-rank} {r2-rank} l2ger2 p2 x2 l2 r2)
        | ge _
        | lhNode {lm-rank} {.(r1-rank + r2-rank)} em pm xm lm rm
        with order l2-rank (r1-rank + (suc r2-rank))
lhMerge {A} {suc .r1-rank} {suc .r2-rank}
        (lhNode {l1-rank} {r1-rank} l1ger1 p1 x1 l1 r1)
        (lhNode {l2-rank} {r2-rank} l2ger2 p2 x2 l2 r2)
        | ge _
        | lhNode {lm-rank} {.(r1-rank + r2-rank)} em pm xm lm rm
        | ge l2≥rm
        = lhNode l2≥rm p2 x2 l2 (subst (LHeap A) (+suc r1-rank r2-rank) (lhNode em pm xm lm rm))
lhMerge {A} {suc .r1-rank} {suc .r2-rank}
        (lhNode {l1-rank} {r1-rank} l1ger1 p1 x1 l1 r1)
        (lhNode {l2-rank} {r2-rank} l2ger2 p2 x2 l2 r2)
        | ge _
        | lhNode {lm-rank} {.(r1-rank + r2-rank)} em pm xm lm rm
        | le rm≥l2
        = lhNode (≥suc (+suc r1-rank r2-rank)) p2 x2 (lhNode em pm xm lm rm) {!!}
lhMerge {A} {suc .r1-rank} {suc .r2-rank}
        (lhNode {l1-rank} {r1-rank} l1ger1 p1 x1 l1 r1)
        (lhNode {l2-rank} {r2-rank} l2ger2 p2 x2 l2 r2)
        | le x = {!!}

--lhMerge {A} {suc l} {suc r} (lhNode l1ger1 p1 x1 l1 r1) (lhNode l2ger2 p2 x2 l2 r2)
--  | ge x | lhNode em pm xm lm rm = ?
--  = lhNode {!!} p2 x2 l2 {!lhNode em pm xm lm rm!}
--  = makeT p2 x2 l2 (lhMerge {!lhNode l1ger1 p1 x1 l1 r1!} r2)
--  = lhNode {!!} p2 x2 l2 (lhMerge {!! lhNode l1ger1 p1 x1 l1 r1 !} r2)
--  = {!!} --makeT p1 x1 l1 (lhMerge {!l1!} (lhNode l2ger2 p2 x2 l2 r2))

{-
-- a simple fact - this is lhNode constructor, we don't need makeT
makeT : {A : Set} {l r : Nat} → l ≥ r → Priority → A → LHeap A l → LHeap A r → LHeap A (suc r)
makeT lger p x l r = lhNode lger p x l r

-- old version, no proofs
lhMerge : {A : Set} {n m : Nat} → LHeap A n → LHeap A m → LHeap A (n + m)
lhMerge lhEmpty h = h
lhMerge {A} {n} {zero} h lhEmpty rewrite rightIdentity n = h -- need to understand this
lhMerge (lhNode p1 x1 l1 r1) (lhNode p2 x2 l2 r2) =
  if p1 < p2
  then makeT p1 x1 l1 (lhMerge r1 (lhNode p2 x2 l2 r2))
  else makeT p2 x2 l2 (lhMerge (lhNode p1 x1 l1 r1) r2) -- commutativity of addition?

lhDeleteMin : {A : Set} {n : Nat} → LHeap A (suc n) → LHeap A ???
lhDeleteMin lhEmpty = {!!} -- can't insert anything here!
lhDeleteMin (lhNode _ _ _ l r) = lhMerge l r
-}

{-
-- can't write this instance declaration now :-/
lHeap : ∀ {n} → Heap λ A → LHeap A n
lHeap = record { empty     = {!!};
                 isEmpty   = lhIsEmpty;
                 singleton = {!!} --lhSingleton
--                 merge     = lhMerge;
--                 insert    = lhInsert;
--                 findMin   = lhFindMin;
--                 deleteMin = lhDeleteMin
               }

-}
