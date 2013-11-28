----------------------------------------------------------------------
-- Copyright: 2013, Jan Stolarek, Lodz University of Technology     --
--                                                                  --
-- License: See LICENSE file in root of the repo                    --
-- Repo address: https://github.com/jstolarek/dep-typed-wbl-heaps   --
--                                                                  --
-- Basic implementation of weight-biased leftist heap. No proofs    --
-- and no dependent types.                                          --
----------------------------------------------------------------------

module MakeT.NoProofs where

open import Basics.Nat
open import Basics hiding (_≥_)

-- Note that we explicitly store rank of a node inside its constructor.
-- Later we will turn it into an inductive family index.
data Heap (A : Set) : Set where
  empty : Heap A
  node  : A → Priority → Rank → Heap A → Heap A → Heap A

-- Returns rank of node
rank : {A : Set} → Heap A → Nat
rank empty            = zero
rank (node _ _ r _ _) = r

-- Creates heap containing a single element with a give priority
singleton : {A : Set} → A → Priority → Heap A
singleton x p = node x p one empty empty

-- makeT takes an element with its priority and two heaps (trees). It
-- constructs a new heap with element at the root and two heaps as
-- children. makeT ensures that WBL heap rank invariant is maintained
-- in the newly created tree by reversing left and right subtrees when
-- necessary.
makeT : {A : Set} → A → Priority → Heap A → Heap A → Heap A
makeT x p l r with rank l ≥ rank r
makeT x p l r | true  = node x p (suc (rank l + rank r)) l r
makeT x p l r | false = node x p (suc (rank l + rank r)) r l

-- merge combines two heaps into one. There are two base cases and two
-- recursive cases. Recursive cases call makeT to ensure that rank
-- invariant is maintained after merging.
merge : {A : Set} → Heap A → Heap A → Heap A
merge h1 h2 with h1 | h2
merge h1 h2
  | empty
  | _
  = h1
merge h1 h2
  | _
  | empty
  = h2
merge h1 h2
  | (node x1 p1 w1 l1 r1)
  | (node x2 p2 w2 l2 r2)
  with p1 < p2
merge h1 h2
  | (node x1 p1 w1 l1 r1)
  | (node x2 p2 w2 l2 r2)
  | true
  = makeT x1 p1 l1 (merge r1 h2)
merge h1 h2
  | (node x1 p1 w1 l1 r1)
  | (node x2 p2 w2 l2 r2)
  | false
  = makeT x2 p2 l2 (merge h1 r2)

-- Inserting is performed by merging heap with newly created singleton heap
insert : {A : Set} → A → Priority → Heap A → Heap A
insert x p h = merge (singleton x p) h

-- Returns element with lowest priority, ie. root element. Here we
-- encounter first serious problem: we can't return anything for empty
-- node. If this was Haskell we could throw an error, but Agda is a
-- total language. This means that every program written in Agda
-- eventually terminates and produces a result. Throwing errors is not
-- allowed.
findMin : {A : Set} → Heap A → A
findMin empty            = {!!} -- can't insert anything here!
findMin (node x _ _ _ _) = x

-- Removes the element with the lowest priority by merging subtrees of
-- a root element. Again, there case of empty heap is problematic. We
-- could give it semantics by returning empty, but this just doesn't
-- fell right. Why should we be able to remove elements from the empty
-- heap?
deleteMin : {A : Set} → Heap A → Heap A
deleteMin empty            = {!!} -- should we insert empty?
deleteMin (node _ _ _ l r) = merge l r
