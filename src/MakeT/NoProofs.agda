----------------------------------------------------------------------
-- Copyright: 2013, Jan Stolarek, Lodz University of Technology     --
--                                                                  --
-- License: See LICENSE file in root of the repo                    --
-- Repo address: https://github.com/jstolarek/dep-typed-wbl-heaps   --
--                                                                  --
-- Basic implementation of weight-biased leftist heap. No proofs    --
-- and no dependent types.                                          --
----------------------------------------------------------------------

{-# OPTIONS --sized-types #-}
module MakeT.NoProofs where

open import Basics.Nat
open import Basics hiding (_≥_)
open import Sized

-- A Heap usually stores elements of some type (Set) A with an assigned
-- priority. To keep our proofs easier to read we will only store
-- Priorities. Priority is a Natural number.
--
-- CONVENTION: Lower number means higher Priority. Therefore the highest
-- Priority is zero. It will sometimes be more convenient not to use this
-- inversed terminology. We will then use terms "smaller" and "greater" (in
-- contrast to "lower" and "higher"). Example: Priority 3 is higher than 5, but
-- 3 is smaller than 5.
--
-- Note that in this Heap we explicitly store rank of a node inside its
-- constructor. Later we will turn it into an inductive family index.

-- We use sized types to help the termination checker see that merging function
-- is total. TODO: Write some more.
data Heap : {i : Size} → Set where
  empty : {i : Size} → Heap {↑ i}
  node  : {i : Size} → Priority → Rank → Heap {i} → Heap {i} → Heap {↑ i}

-- Returns rank of node
rank : Heap → Nat
rank empty            = zero
rank (node _ r _ _) = r

-- Creates heap containing a single element with a give priority
singleton : Priority → Heap
singleton p = node p one empty empty

-- Note [Merging algorithm]
-- ~~~~~~~~~~~~~~~~~~~~~~~~
--
-- We use a two-pass merging algorithm. One pass, implemented by
-- merge, performs merging in a top-down manner. Second one,
-- implemented by makeT, ensures that invarinats of weight-biased
-- leftist tree are not violated by creating a node fulfilling the
-- invariant.
--
-- Merge function analyzes four cases cases. Two of them are bases
-- cases:
--
--    a) h1 is empty - return h2
--
--    b) h2 is empty - return h1
--
-- The other two form the inductive definition of merge:
--
--    c) p1 < p2, in which case p1 becomes the root, l1 becomes its
--       one child and result of merging r1 with h2 becomes the other
--       child:
--
--               p1
--              /  \
--             /    \
--            l1  r1+h2
--
--    d) p2 < p1, in which case p2 becomes the root, l2 becomes its
--       one child and result of merging r2 with h1 becomes the other
--       child.
--
--               p2
--              /  \
--             /    \
--            l2  r2+h1
--
-- In inductive cases we pass both childred - i.e. either l1 and r1+h2
-- or l2 and r2+h1 - to makeT which creates a new node by inspecting
-- sizes of children and swapping them if necessary.


-- makeT takes an element with its priority and two heaps (trees). It
-- constructs a new heap with element at the root and two heaps as
-- children. makeT ensures that WBL heap rank invariant is maintained
-- in the newly created tree by reversing left and right subtrees when
-- necessary.
makeT : Priority → Heap → Heap → Heap
makeT p l r with rank l ≥ rank r
makeT p l r | true  = node p (suc (rank l + rank r)) l r
makeT p l r | false = node p (suc (rank l + rank r)) r l

-- merge combines two heaps into one. There are two base cases and two recursive
-- cases. Recursive cases call makeT to ensure that rank invariant is maintained
-- after merging.
merge : {i : Size} → Heap {i} → Heap {i} → Heap
merge empty h2 = h2
merge h1 empty = h1
merge (node p1 w1 l1 r1) (node p2 w2 l2 r2) with p1 < p2
merge (node p1 w1 l1 r1) (node p2 w2 l2 r2)
  | true  = makeT p1 l1 (merge r1 (node p2 w2 l2 r2))
merge (node p1 w1 l1 r1) (node p2 w2 l2 r2)
  | false = makeT p2 l2 (merge (node p1 w1 l1 r1) r2)

-- Inserting is performed by merging heap with newly created singleton heap
insert : Priority → Heap → Heap
insert p h = merge (singleton p) h

-- Returns element with lowest priority, ie. root element. Here we
-- encounter first serious problem: we can't return anything for empty
-- node. If this was Haskell we could throw an error, but Agda is a
-- total language. This means that every program written in Agda
-- eventually terminates and produces a result. Throwing errors is not
-- allowed.
findMin : Heap → Priority
findMin empty          = {!!} -- can't insert anything here!
findMin (node p _ _ _) = p

-- Removes the element with the lowest priority by merging subtrees of
-- a root element. Again, there case of empty heap is problematic. We
-- could give it semantics by returning empty, but this just doesn't
-- feel right. Why should we be able to remove elements from the empty
-- heap?
deleteMin : Heap → Heap
deleteMin empty            = {!!} -- should we insert empty?
deleteMin (node _ _ l r) = merge l r

-- As a quick sanity check let's construct some examples. Here's a heap
-- constructed by inserting following priorities into an empty heap: 3, 0, 1, 2.
heap : Heap
heap = insert (suc (suc zero))
      (insert (suc zero)
      (insert zero
      (insert (suc (suc (suc zero))) empty)))

-- Example usage of findMin
findMinInHeap : Priority
findMinInHeap = findMin heap

-- Example usage of deleteMin
deleteMinFromHeap : Heap
deleteMinFromHeap = deleteMin heap
