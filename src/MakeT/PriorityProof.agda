----------------------------------------------------------------------
-- Copyright: 2013, Jan Stolarek, Lodz University of Technology     --
--                                                                  --
-- License: See LICENSE file in root of the repo                    --
-- Repo address: https://github.com/jstolarek/dep-typed-wbl-heaps   --
--                                                                  --
-- Dependently-typed implementation of weight-biased leftist heap.  --
-- Two-stage heap merging algorithm using auxiliary makeT function  --
-- (see Okasaki, Chapter 3.1, pp. 17-19)                            --
-- Proof of preserving correctness of priorities.                   --
----------------------------------------------------------------------

module MakeT.PriorityProof where

open import Basics

Priority : Set
Priority = Nat

-- We have to use rank again
Rank : Set
Rank = Nat

-- As we shall see it becomes a problem that Heap does not have any
-- information about its children.
data Heap (A : Set) : Nat → Set where
  empty : {n : Nat} → Heap A n
  node  : {n : Nat} → A → (p : Priority) → Rank → p ≥ n  → Heap A p → Heap A p → Heap A n

rank : {A : Set} {n : Nat} → Heap A n → Nat
rank empty            = zero
rank (node _ _ r _ _ _) = r

isEmpty : {A : Set} {n : Nat} → Heap A n → Bool
isEmpty empty            = true
isEmpty (node _ _ _ _ _ _) = false

-- singletonL is liberal: it says that every element in that singleton
-- Heap is greater than 0, but that is trivial, since any natural
-- number is.
singletonL : {A : Set} → A → (p : Priority) → Heap A zero
singletonL x p = node x p one ge0 empty empty

-- Singleton is conservative. It says that every element in that
-- singleton tree is greater or equal to p.
singletonC : {A : Set} → A → (p : Priority) → Heap A p
singletonC x p = node x p one (≥sym refl) empty empty

makeT : {A : Set} {n : Nat} → A → (p : Priority) → p ≥ n → Heap A p → Heap A p → Heap A n
makeT x p pgen l r with rank l | rank r
makeT x p pgen l r | l-rank | r-rank with order l-rank r-rank
makeT x p pgen l r | l-rank | r-rank | ge _ = node x p (suc (l-rank + r-rank)) pgen l r
makeT x p pgen l r | l-rank | r-rank | le _ = node x p (suc (l-rank + r-rank)) pgen r l

merge : {A : Set} {b : Nat} → Heap A b → Heap A b → Heap A b
merge h1 h2 with h1 | h2
merge h1 h2
          | empty
          | _
          = h2
merge h1 h2
          | _
          | empty
          = h1
merge h1 h2
          | node x1 p1 l-rank p1≥b l1 r1
          | node x2 p2 r-rank p2≥b l2 r2
          with order p1 p2
merge h1 h2
          | node x1 p1 l-rank p1≥b l1 r1
          | node x2 p2 r-rank p2≥b l2 r2
          | le p1≤p2
          = makeT x1 p1 p1≥b l1 (merge r1 (node x2 p2 r-rank p1≤p2 l2 r2))
merge h1 h2
          | node x1 p1 l-rank p1≥b l1 r1
          | node x2 p2 r-rank p2≥b l2 r2
          | ge p1≥p2
          = makeT x2 p2 p2≥b l2 (merge r2 (node x1 p1 l-rank p1≥p2 l1 r1))

-- Again, termination checker problems. I can't create a function that
-- just replaces the proof, because Heap's index doesn't say anything
-- about index of its children and the new proof refers to index of
-- children.

toZero : {A : Set} {n : Nat} → Heap A n → Heap A zero
toZero empty                 = empty
toZero (node x p rank _ l r) = node x p rank ge0 l r

insertL : {A : Set} {n : Nat} → A → Priority → Heap A n → Heap A zero
insertL x p h = merge (singletonL x p) (toZero h)

-- This feels too conservative
insertC : {A : Set} → A → (p : Priority) → Heap A p → Heap A p
insertC x p h = merge (singletonC x p) h

-- We could write this function, but it would be very inconvenient to
-- require a proof each time we want to insert something.
insert : {A : Set} {n : Nat} → A → (p : Priority) → n ≥ p → Heap A n → Heap A p
insert x p n≥p h = merge {!!} {!!}

-- Again, findMin and deletMin are incomplete
findMin : {A : Set} {n : Nat} → Heap A n → A
findMin empty              = {!!}
findMin (node x _ _ _ _ _) = x

deleteMin : {A : Set} {n b : Nat} → Heap A n → Heap A zero
deleteMin empty                               = {!!}
deleteMin {A} {n} {b} (node x p rank p≥n l r) = merge (toZero l) (toZero r)
