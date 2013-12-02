----------------------------------------------------------------------
-- Copyright: 2013, Jan Stolarek, Lodz University of Technology     --
--                                                                  --
-- License: See LICENSE file in root of the repo                    --
-- Repo address: https://github.com/jstolarek/dep-typed-wbl-heaps   --
--                                                                  --
-- Weight biased leftist heap that proves to maintain priority      --
-- invariant: priority at the node is not larger than priorities of --
-- its two children.                                                --
----------------------------------------------------------------------

{-# OPTIONS --sized-types #-}
module MakeT.PriorityProof where

open import Basics.Nat renaming (_≥_ to _≥ℕ_)
open import Basics
open import Sized

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
data Heap : {i : Size} → Priority → Set where
  empty : {i : Size} {n : Priority} → Heap {↑ i} n
  node  : {i : Size} {n : Priority} → (p : Priority) → Rank → p ≥ n →
          Heap {i} p → Heap {i} p → Heap {↑ i} n

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
merge : {i : Size} {p : Nat} → Heap {i} p → Heap {i} p → Heap p
merge empty h2 = h2
merge h1 empty = h1
merge .{↑ i} (node .{i} p1 l-rank p1≥p l1 r1) (node {i} p2 r-rank p2≥p l2 r2) with order p1 p2
merge .{↑ i} (node .{i} p1 l-rank p1≥p l1 r1) (node {i} p2 r-rank p2≥p l2 r2) | le p1≤p2
  = makeT p1 p1≥p l1 (merge r1 (node p2 r-rank p1≤p2 l2 r2))
merge .{↑ i} (node .{i} p1 l-rank p1≥p l1 r1) (node {i} p2 r-rank p2≥p l2 r2) | ge p1≥p2
  = makeT p2 p2≥p l2 (merge r2 (node p1 l-rank p1≥p2 l1 r1))

-- When writing indexed insert function we once again have to answer a
-- question of how to index input and output Heap. The easiest
-- solution is to be liberal: let the input and output Heap have no
-- limitations on Priorities they can store. In other words, let they
-- be indexed by zero:
insert : Priority → Heap zero → Heap zero
insert p h = merge (singleton p) h

-- Now we can create an example heap. The only difference between this
-- heap and the heap without any proofs is that we need to explicitly
-- instantiate implicit parameter to empty constructor.
heap : Heap zero
heap = insert (suc (suc zero))
      (insert (suc zero)
      (insert zero
      (insert (suc (suc (suc zero))) (empty {n = zero}))))

-- What if we actaully want to enforce bounds imposed on the heap by its index?
-- In that situation we are required to provide proof that the index we are
-- inserting into the Heap can really be insterted into it. To do this we will
-- need a few additional functions. First of all we need a new singleton
-- function that will construct a singleton Heap with a bound (this requires us
-- to supply additional parameter that is evidence that priority we just
-- inserted into our singleton heap is lower than the bound).
singletonE : {n : Priority} → (p : Priority) → p ≥ n → Heap n
singletonE p pr = node p one pr empty empty

-- We need a proof of transitivity of ≥. Our base case is:
--
--  a ≥ b ∧ b ≥ 0 ⇒ a ≥ 0
--
-- In other words if c is 0 then ge0 proofs the property. If c is not zero, then
-- b is also not zero (by definitions of data constructors of ≥) and hence a is
-- also not zero. This gives us second equation that is a recursive proof on
-- ≥trans.
≥trans : {a b c : Nat} → a ≥ b → b ≥ c → a ≥ c
≥trans a≥b        ge0      = ge0
≥trans (geS a≥b) (geS b≥c) = geS (≥trans a≥b b≥c)

-- Having prooved the transitivity of ≥ we can construct a function that loosens
-- the bound we put on a heap. If we have a heap with a bound p - meaning that
-- all priorities in a heap are guaranteed to be lower than or equal to p - and
-- we also have evidence than n is a priority higher than p then we can change
-- the restriction on the heap so that it accepts higher priorites. For example
-- if we have Heap 5, ie. all elements in the heap are 5 or greater, and we have
-- evidence that 5 ≥ 3, then we can convert Heap 5 to Heap 3. Note how we are
-- prevented from writing wrong code: if we have Heap 3 we cannot convert it to
-- Heap 5. This is not possible in theory: Heap 3 may contain 4, but Heap 5 is
-- expected to contain elements not smaller than 5. It is also not possible
-- practically: thanks to our definition of ≥ we can't orivude evidence that
-- 3 ≥ 5.
liftBound : {p b : Priority} → b ≥ p → Heap b → Heap p
liftBound b≥n empty = empty
liftBound b≥n (node p rank p≥b l r)
  = node p rank (≥trans p≥b b≥n) l r

-- With singletonE and liftBound we can construct insert function that allows to
-- insert element with priority p into a Heap bound by n, but only if we can
-- supply evidence that p ≥ n, ie. that p can actually be stored in the heap.
insertE : {n : Priority} → (p : Priority) → p ≥ n → Heap p → Heap n
insertE p p≥n h = merge (singletonE p p≥n) (liftBound p≥n h)

-- Again, findMin and deletMin are incomplete
findMin : {b : Priority} → Heap b → Priority
findMin empty            = {!!}
findMin (node p _ _ _ _) = p

-- deleteMin requires a bit more work than previously. First, notice that the
-- bound placed on the input and output heaps is the same. This happens because
-- relation between priorities in a node and it's children is ≥, not >
-- (ie. equality is allowed). We cannot therefore guearantee that bound on
-- priority will increase after removing highest-priority element from the Heap.
-- When we merge left and right subtrees we need to lift their bounds so they
-- are now both b (not p).
deleteMin : {b : Priority} → Heap b → Heap b
deleteMin empty                 = {!!}
deleteMin (node p rank p≥b l r) = merge (liftBound p≥b l) (liftBound p≥b r)
