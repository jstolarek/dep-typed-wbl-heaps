----------------------------------------------------------------------
-- Copyright: 2013, Jan Stolarek, Lodz University of Technology     --
--                                                                  --
-- License: See LICENSE file in root of the repo                    --
-- Repo address: https://github.com/jstolarek/dep-typed-wbl-heaps   --
--                                                                  --
-- Basic implementation of weight-biased leftist heap. No proofs    --
-- and no dependent types. Uses a two-pass merging algorithm.       --
----------------------------------------------------------------------

{-# OPTIONS --sized-types #-}
module TwoPassMerge.NoProofs where

open import Basics.Nat
open import Basics hiding (_≥_)
open import Sized

-- Weight biased leftist heap is implemented using a binary tree. I
-- will interchangeably refer to children of a node as "subtrees" or
-- "subheaps".
--
-- A Heap usually stores elements of some type (Set) A with an
-- assigned priority. However to keep code easier to read each node
-- will only store Priority (a natural number). This will not affect
-- in any way proofs that we are conducting.

-- We begin with a simple implementation that uses no dependent
-- types. Note the we explicitly store rank in node constructor
-- (recall that rank is defined as number of elements in a
-- tree). Theoretically this information is redundant - we could
-- compute the size of a tree whenever we need it. The reason I choose
-- to store it in a node is that later, when we come to proving the
-- rank invariant, it will be instructive to show how information
-- stored inside a constructor is turned into an inductive family
-- index.

-- One more thing to note is that we will define most of our Heaps to
-- be sized types, ie. to use an implict index that defines how a
-- constructor affects the inductive size of the data structure. This
-- information is used to guide the termination checker in the
-- definitions of merge.
data Heap : {i : Size} → Set where
  empty : {i : Size} → Heap {↑ i}
  node  : {i : Size} → Priority → Rank → Heap {i} → Heap {i} → Heap {↑ i}

-- Returns rank of node.
rank : Heap → Nat
rank empty          = zero
rank (node _ r _ _) = r

-- Creates heap containing a single element with a given Priority
singleton : Priority → Heap
singleton p = node p one empty empty

-- Note [Two-pass merging algorithm]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
-- We use a two-pass implementation of merging algorithm. One pass,
-- implemented by merge, performs merging in a top-down manner. Second
-- one, implemented by makeT, ensures that rank invariant of weight
-- biased leftist tree is not violated after merging.
--
-- Notation:
--
--  h1, h2 - heaps being merged
--  p1, p2 - priority of root element in h1 and h2
--  l1     - left  subtree in the first  heap
--  r1     - right subtree in the first  heap
--  l2     - left  subtree in the second heap
--  r2     - right subtree in the second heap
--
-- Merge function analyzes four cases. Two of them are base cases:
--
--    a) h1 is empty - return h2
--
--    b) h2 is empty - return h1
--
-- The other two form the inductive definition of merge:
--
--    c) priority p1 is higher than p2 - p1 becomes new root, l1
--       becomes its one child and result of merging r1 with h2
--       becomes the other child:
--
--               p1
--              /  \
--             /    \
--            l1  r1+h2 -- here "+" denotes merging
--
--    d) priority p2 is higher than p2 - p2 becomes new root, l2
--       becomes its one child and result of merging r2 with h1
--       becomes the other child.
--
--               p2
--              /  \
--             /    \
--            l2  r2+h1
--
-- Note that there is no guarantee that rank of r1+h2 (or r2+h1) will
-- be smaller than rank of l1 (or l2). To ensure that merged heap
-- maintains the rank invariant we pass both childred - ie. either l1
-- and r1+h2 or l2 and r2+h1 - to makeT, which creates a new node by
-- inspecting sizes of children and swapping them if necessary.

-- makeT takes an element (priority) and two heaps (trees). It
-- constructs a new heap with element at the root and two heaps as
-- children. makeT ensures that WBL heap rank invariant is maintained
-- in the newly created tree by reversing left and right subtrees when
-- necessary (note the inversed r and l in the last case of makeT).
makeT : Priority → Heap → Heap → Heap
makeT p l r with rank l ≥ rank r
makeT p l r | true  = node p (suc (rank l + rank r)) l r
makeT p l r | false = node p (suc (rank l + rank r)) r l

-- merge combines two heaps into one. There are two base cases and two
-- recursive cases - see [Two-pass Merging algorithm]. Recursive cases
-- call makeT to ensure that rank invariant is maintained after
-- merging.
merge : {i j : Size} → Heap {i} → Heap {j} → Heap
merge empty h2 = h2
merge h1 empty = h1
merge (node p1 h1-r l1 r1) (node p2 h2-r l2 r2)
  with p1 < p2
merge (node p1 h1-r l1 r1) (node p2 h2-r l2 r2)
  | true  = makeT p1 l1 (merge r1 (node p2 h2-r l2 r2))
merge (node p1 h1-r l1 r1) (node p2 h2-r l2 r2)
  | false = makeT p2 l2 (merge (node p1 h1-r l1 r1) r2)

-- Inserting into a heap is performed by merging that heap with newly
-- created singleton heap.
insert : Priority → Heap → Heap
insert p h = merge (singleton p) h

-- findMin returns element with highest priority, ie. root
-- element. Here we encounter first serious problem: we can't return
-- anything for empty node. If this was Haskell we could throw an
-- error, but Agda is a total language. This means that every program
-- written in Agda eventually terminates and produces a
-- result. Throwing errors is not allowed.
findMin : Heap → Priority
findMin empty          = {!!}  -- does it make sense to assume default
                               -- priority for empty heap?
findMin (node p _ _ _) = p

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just    : A → Maybe A

findMinM : Heap → Maybe Priority
findMinM empty          = nothing
findMinM (node p _ _ _) = just p


-- deleteMin removes the element with the highest priority by merging
-- subtrees of a root element. Again the case of empty heap is
-- problematic. We could give it semantics by returning empty, but
-- this just doesn't feel right. Why should we be able to remove
-- elements from the empty heap?
deleteMin : Heap → Heap
deleteMin empty          = {!!} -- should we insert empty?
deleteMin (node _ _ l r) = merge l r

-- As a quick sanity check let's construct some examples. Here's a
-- heap constructed by inserting following priorities into an empty
-- heap: 3, 0, 1, 2.
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
