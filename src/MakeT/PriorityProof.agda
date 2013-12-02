----------------------------------------------------------------------
-- Copyright: 2013, Jan Stolarek, Lodz University of Technology     --
--                                                                  --
-- License: See LICENSE file in root of the repo                    --
-- Repo address: https://github.com/jstolarek/dep-typed-wbl-heaps   --
--                                                                  --
-- Weight biased leftist heap that proofs to maintain priority      --
-- invariant: priority at the node is not larger than priorities of --
-- its two children.                                                --
--                                                                  --
----------------------------------------------------------------------

module MakeT.PriorityProof where

open import Basics.Nat renaming (_≥_ to _≥ℕ_)
open import Basics


-- To proof the invariant we will index nodes using Priority. Index of
-- value n says that "this heap can store elements with priorities n
-- or lower" (remember that lower priority means larger Nat). In other
-- words heap indexed with 0 can store any Priority, while heap
-- indexed with 3 can store priorities 3, 4 and lower, but can't store
-- 0, 1 and 2.
--
-- As previously, Heap has two constructors:
--
--  1) empty simply returns Heap n, where index n is not constrained
--     in any way. This means that empty heap can store any Priority.
--
--  2) node also creates Heap n, but this time n is constrained: n
--     must not be greater than p, where p is index of node's
--     children. This means "if you create a Heap storing Priority p
--     as its root element then the resulting Heap will only be able
--     to store priorities higher than p (higher priorities = smaller
--     Nats)".
--
-- The most important thing here is that in order to create a node we
-- need to supply a proof that priorities possible to store in
-- children nodes are not higher than priority that can be stored in
-- the node itself. That proof takes a form of a datatype (≥). If we
-- can construct a value of type (p ≥ n) then existance of such a
-- value becomes a proof that p is greater-equal to n.
--
-- Note that both left and right subtree of node are indexed with p.
-- This means that element at the node has priority at least as
-- high as its children.
--
-- As we shall see it becomes a problem that Heap does not have any
-- information about its children.
data Heap : Priority → Set where
  empty : {n : Priority} → Heap n
  node  : {n : Priority} → (p : Priority) → Rank → p ≥ n  → Heap p → Heap p → Heap n

-- Again, we need a function to extract rank from a node
rank : {n : Nat} → Heap n → Nat
rank empty            = zero
rank (node _ r _ _ _) = r

-- The first question is how to create a singleton heap, ie. a Heap
-- storing one element. The question we need to answer is "what
-- Priorities can we later store in a singleton Heap?". "Any" seems
-- to be a reasonable answer. This means the resulting Heap will be
-- indexed with zero, meaning "Priorities lower or equal to zero can be
-- stored in this Heap" (remember that any priority is lower or equal
-- to zero). This leads us to following definition:
singleton : (p : Priority) → Heap zero
singleton p = node p one ge0 empty empty

-- We can imagine we would like to limit the range of priorities we
-- can insert into a singleton Heap. This means the resulting Heap
-- would be index with some n (the bound on allowed Priority
-- values). In such case however we are required to supply a proof
-- than p ≥ n. This would lead us to a definition like this:
--
-- singletonP : {n : Nat} → (p : Priority) → p ≥ n → Heap n
-- singletonP p p≥n = node p one p≥n empty empty

-- makeT now returns indexed heaps, so it requires one more parameter:
-- a proof that priorities stored in resulting heap are not lower than
-- in the subheaps.
makeT : {n : Nat} → (p : Priority) → p ≥ n → Heap p → Heap p → Heap n
makeT p pgen l r with rank l ≥ℕ rank r
makeT p pgen l r | true  = node p (suc (rank l + rank r)) pgen l r
makeT p pgen l r | false = node p (suc (rank l + rank r)) pgen r l

-- The important change in merge is that now we don't compare node
-- priorities using an operator that returns Bool. We compare them
-- using "order" function that not only returns result of comparison,
-- but also supplies a proof of the result. This proof tells us
-- something important about the relationship between p1, p2 and
-- priority of the merged Heap. Note that we use the new proof to
-- reconstruct one of the heaps that is passed in recursive call to
-- merge.
merge : {p : Nat} → Heap p → Heap p → Heap p
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
          | node p1 l-rank p1≥p l1 r1
          | node p2 r-rank p2≥p l2 r2
          with order p1 p2
merge h1 h2
          | node p1 l-rank p1≥p l1 r1
          | node p2 r-rank p2≥p l2 r2
          | le p1≤p2
          = makeT p1 p1≥p l1 (merge r1 (node p2 r-rank p1≤p2 l2 r2))
merge h1 h2
          | node p1 l-rank p1≥p l1 r1
          | node p2 r-rank p2≥p l2 r2
          | ge p1≥p2
          = makeT p2 p2≥p l2 (merge r2 (node p1 l-rank p1≥p2 l1 r1))

-- Again, termination checker problems. I can't create a function that
-- just replaces the proof, because Heap's index doesn't say anything
-- about index of its children and the new proof refers to index of
-- children.

toZero : {n : Nat} → Heap n → Heap zero
toZero empty               = empty
toZero (node p rank _ l r) = node p rank ge0 l r

insert : {n : Nat} → Priority → Heap n → Heap zero
insert p h = merge (singleton p) (toZero h)

heap : Heap zero
heap = insert (suc (suc zero))
      (insert (suc zero)
      (insert zero
      (insert (suc (suc (suc zero))) (empty {n = zero}))))

-- We could write this function, but it would be very inconvenient to
-- require a proof each time we want to insert something.
--insert : {n : Nat} → (p : Priority) → n ≥ p → Heap n → Heap p
--insert p n≥p h = merge {!!} {!!}

-- Again, findMin and deletMin are incomplete
findMin : {n : Nat} → Heap n → Priority
findMin empty            = {!!}
findMin (node p _ _ _ _) = p

deleteMin : {n : Nat} → Heap n → Heap zero
deleteMin empty                 = {!!}
deleteMin (node p rank p≥n l r) = merge (toZero l) (toZero r)
