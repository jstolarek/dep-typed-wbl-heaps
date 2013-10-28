----------------------------------------------------------------------
-- Copyright: 2013, Jan Stolarek, Lodz University of Technology     --
--                                                                  --
-- License: See LICENSE file in root of the repo                    --
-- Repo address: https://github.com/jstolarek/dep-typed-heaps       --
--                                                                  --
-- Dependently-typed implementation of Heap. Work in progress.      --
----------------------------------------------------------------------

module DepTypedHeap where

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
-}
    deleteMin : ∀ {A} → H A → H A
open Heap {{...}} public


data LHeap (A : Set) : Nat → Set where
  lhEmpty : LHeap A zero
  lhNode  : {m n : Nat} → Nat → A → LHeap A m → LHeap A n → LHeap A (suc n)

{-
-- we don't need rank. Now we have dependent types

rank : {A : Set} {n : Nat} → LHeap A n -> n
rank lhEmpty = zero
rank (lhNode r _ _ _ _) = r
-}

lhIsEmpty : {A : Set} {n : Nat} → LHeap A n → Bool
lhIsEmpty {A} {zero} lhEmpty           = true
lhIsEmpty {A} {suc n} (lhNode _ _ _ _) = false

lhSingleton : {A : Set} → Nat → A → LHeap A (suc zero)
lhSingleton p x = lhNode p x lhEmpty lhEmpty

makeT : {A : Set} {n m : Nat} → Nat → A → LHeap A n → LHeap A m → LHeap A (suc (min n m))
makeT {A} {n} {m} p x l r with n ≥ m
makeT p x l r | true  = lhNode p x l r
makeT p x l r | false = lhNode p x r l

lhMerge : {A : Set} {n m : Nat} → LHeap A n → LHeap A m → LHeap A (n + m)
lhMerge lhEmpty h = h
lhMerge {A} {n} {zero} h lhEmpty rewrite rightIdentity n = h -- need to understand this
lhMerge (lhNode p1 x1 l1 r1) (lhNode p2 x2 l2 r2) =
  if p1 < p2
  then makeT p1 x1 l1 (lhMerge r1 (lhNode p2 x2 l2 r2))
  else makeT p2 x2 l2 (lhMerge (lhNode p1 x1 l1 r1) r2) -- commutativity of addition?

{-
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
