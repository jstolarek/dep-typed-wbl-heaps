----------------------------------------------------------------------
-- Copyright: 2013, Jan Stolarek, Lodz University of Technology     --
--                                                                  --
-- License: See LICENSE file in root of the repo                    --
-- Repo address: https://github.com/jstolarek/dep-typed-heaps       --
--                                                                  --
-- Dependently-typed implementation of weight-biased leftist heap.  --
-- Two-stage heap merging algorithm using auxiliary makeT function  --
-- (see Okasaki, Chapter 3.1, pp. 17-19)                            --
-- Proof of preserving correctness of priorities.                   --
----------------------------------------------------------------------

module DepTypedWeightedHeapMakeTHeapProperty where

open import DepTypedBasics

Priority : Set
Priority = Nat

-- We have to use rank again
Rank : Set
Rank = Nat

-- We use dependent types to index a tree by its size, instead of
-- explicitly storing the size in the node constructor. Size of a tree
-- equals size of its children plus one. Additionally we store
-- evidence that a tree represents correct weight-biased leftist heap
-- i.e. that size of left subtree is at least as large as size of the
-- right one.
data Heap (A : Set) : Nat → Set where
  empty : {n : Nat} → Heap A n
  node  : {n : Nat} → A → (p : Priority) → Rank → p ≥ n  → Heap A p → Heap A p → Heap A n

rank : {A : Set} {n : Nat} → Heap A n → Nat
rank empty            = zero
rank (node _ _ r _ _ _) = r

isEmpty : {A : Set} {n : Nat} → Heap A n → Bool
isEmpty empty            = true
isEmpty (node _ _ _ _ _ _) = false

-- TODO: Is this correct? should I use p or zero for index?
singleton : {A : Set} {n : Nat} → A → (p : Priority) → Heap A n
singleton x p = node x p one {!!} empty empty

makeT : {A : Set} {n : Nat} → A → (p : Priority) → p ≥ n → Heap A p → Heap A p → Heap A n
makeT x p pgen l r with rank l | rank r
makeT x p pgen l r | l-rank | r-rank with order l-rank r-rank
makeT x p pgen l r | l-rank | r-rank | ge _ = node x p (suc (l-rank + r-rank)) pgen l r
makeT x p pgen l r | l-rank | r-rank | le _ = node x p (suc (l-rank + r-rank)) pgen r l

merge : {A : Set} {b : Nat} → Heap A b → Heap A b → Heap A b
merge h1 h2 with h1 | h2
merge {A} {b} h1 h2
          | empty
          | _
          = h2
merge {A} {b} h1 h2
          | _
          | empty
          = h1
merge {A} {b} h1 h2
          | node x1 p1 l-rank p1≥b l1 r1
          | node x2 p2 r-rank p2≥b l2 r2
          with order p1 p2
merge {A} {b} h1 h2
          | node x1 p1 l-rank p1≥b l1 r1
          | node x2 p2 r-rank p2≥b l2 r2
          | le p1≤p2
          = makeT x1 p1 p1≥b l1 (merge r1 (node x2 p2 r-rank p1≤p2 l2 r2))
merge {A} {b} h1 h2
          | node x1 p1 l-rank p1≥b l1 r1
          | node x2 p2 r-rank p2≥b l2 r2
          | ge p1≥p2
          = makeT x2 p2 p2≥b l2 (merge r2 (node x1 p1 l-rank p1≥p2 l1 r1))

insert : {A : Set} → A → (p : Priority) → Heap A p → Heap A p
insert x p h = merge (singleton x p) h

{-
findMin : {A : Set} {n : Nat} → Heap A (suc n) → A
findMin (node _ _ x _ _) = x

deleteMin : {A : Set} {n p : Nat} → Heap A n → Heap A p
deleteMin empty              = {!!}
deleteMin (node _ _ _ _ l r) = merge {!!} {!!}
-}

