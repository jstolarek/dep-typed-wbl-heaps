----------------------------------------------------------------------
-- Copyright: 2013, Jan Stolarek, Lodz University of Technology     --
--                                                                  --
-- License: See LICENSE file in root of the repo                    --
-- Repo address: https://github.com/jstolarek/dep-typed-wbl-heaps   --
--                                                                  --
-- Weight biased leftist heap that proves to maintain priority      --
-- invariant: priority at the node is not lower than priorities of  --
-- its two children. Uses a two-pass merging algorithm.             --
----------------------------------------------------------------------

{-# OPTIONS --sized-types #-}
module TwoPassMerge.PriorityProof where

open import Basics.Nat renaming (_≥_ to _≥ℕ_)
open import Basics
open import Sized

-- Priority invariant says that: for any node in the tree priority in
-- that node is higher than priority stored by its children. This
-- means that any path from root to leaf is ordered (highest priority
-- at the root, lowest at the leaf). This property allows us to
-- construct an efficient merging operation (see paper for more
-- details).
--
-- To prove this invariant we will index nodes using Priority. Index
-- of value n says that "this heap can store elements with priorities
-- n or lower" (remember that lower priority means larger Nat). In
-- other words Heap indexed with 0 can store any Priority, while Heap
-- indexed with 3 can store priorities 3, 4 and lower, but can't store
-- 0, 1 and 2.
--
-- As previously, Heap has two constructors:
--
--  1) empty returns Heap n, where index n is not constrained in any
--     way. This means that empty heap can be given any restriction on
--     priorities of stored elements.
--
--  2) node also creates Heap n, but this time n is constrained. If we
--     store priority p in a node then:

--       a) the resulting heap can only be restricted to store
--          priorities at least as high as p. For example, if we
--          create a node that stores priority 3 we cannot restrict
--          the resulting heap to store priorities 4 and lower,
--          because the fact that we store 3 in that node violates the
--          restriction. This restriction is expressed by the "p ≥ n"
--          parameter: if we can construct a value of type (p ≥ n)
--          then existance of such a value becomes a proof that p is
--          greater-equal to n. We must supply such proof to every
--          node.

--       b) children of a node can only be restricted to store
--          priorities that are not higher than p. Example: if we
--          restrict a node to store priorities 4 and lower we cannot
--          restrict its children to store priorities 3 and
--          higher. This restriction is expressed by index "p" in the
--          subheaps passed to node constructor.

data Heap : {i : Size} → Priority → Set where
  empty : {i : Size} {n : Priority} → Heap {↑ i} n
  node  : {i : Size} {n : Priority} → (p : Priority) → Rank → p ≥ n →
          Heap {i} p → Heap {i} p → Heap {↑ i} n

-- Let's demonstrate that priority invariant cannot be broken. Below
-- we construct a heap like this:
--
--      ?
--     / \
--    /   \
--   E     0
--
-- where E means empty node and 0 means node storing Priority 0 (yes,
-- this heap violates the rank invariant!). We left out the root
-- element. The only value that can be supplied there is zero (try
-- giving one and see that typechecker will not accept it). This is
-- beacuse the value n with which 0 node can be index must obey the
-- restriction 0 ≥ n. This means that 0 node can only be indexed with
-- 0. When we try to construct ? node we are thus only allowed to
-- insert priority 0.
heap-broken : Heap zero
heap-broken = node {!!} (suc one) ge0 empty (node zero one ge0 empty empty)

-- Here is a correct heap. It stores one at the leaf and 0 at the
-- root. It still violates the rank invariant - we deal with that in
-- TwoPassMerge.RankProof.
heap-correct : Heap zero
heap-correct = node zero (suc one) ge0 empty (node one one ge0 empty empty)

-- Again, we need a function to extract rank from a node
rank : {b : Priority} → Heap b → Rank
rank empty            = zero
rank (node _ r _ _ _) = r

-- The first question is how to create a singleton heap, ie. a Heap
-- storing one element. The question we need to answer is "what
-- Priorities can we later store in a singleton Heap?". "Any" seems to
-- be a reasonable answer. This means the resulting Heap will be
-- indexed with zero, meaning "Priorities lower or equal to zero can
-- be stored in this Heap" (remember that any priority is lower or
-- equal to zero). This leads us to following definition:
singleton : (p : Priority) → Heap zero
singleton p = node p one ge0 empty empty

-- We can imagine we would like to limit the range of priorities we
-- can insert into a singleton Heap. This means the resulting Heap
-- would be index with some b (the bound on allowed Priority
-- values). In such case however we are required to supply a proof
-- that p ≥ b. This would lead us to a definition like this:
--
-- singletonB : {b : Priority} → (p : Priority) → p ≥ b → Heap b
-- singletonB p p≥b = node p one p≥b empty empty
--
-- We'll return to that idea soon.

-- makeT now returns indexed heaps, so it requires one more parameter:
-- a proof that priorities stored in resulting heap are not lower than
-- in the subheaps.
makeT : {b : Nat} → (p : Priority) → p ≥ b → Heap p → Heap p → Heap b
makeT p p≥b l r with rank l ≥ℕ rank r
makeT p p≥b l r | true  = node p (suc (rank l + rank r)) p≥b l r
makeT p p≥b l r | false = node p (suc (rank l + rank r)) p≥b r l

-- The important change in merge is that now we don't compare node
-- priorities using an operator that returns Bool. We compare them
-- using "order" function that not only returns result of comparison,
-- but also supplies a proof of the result. This proof tells us
-- something important about the relationship between p1, p2 and
-- priority bound of the merged Heap. Note that we use the new proof
-- to reconstruct one of the heaps that is passed in recursive call to
-- merge. We must do this because by comparing priorities p1 and p2 we
-- learned something new about restriction placed on priorities in one
-- of the heaps and we can now be more precise in expressing these
-- restrictions.
--
-- Note also that despite indexing our data types with Size the
-- termination checker complains that merge function does not
-- terminate. This is not a problem in our definitions but a bug in
-- Agda's implementation. I leave the code in this form in hope that
-- this bug will be fixed in a future release of Agda. For mor details
-- see http://code.google.com/p/agda/issues/detail?id=59#c23
merge : {i j : Size} {p : Nat} → Heap {i} p → Heap {j} p → Heap p
merge empty h2 = h2
merge h1 empty = h1
merge .{↑ i} .{↑ j}
  (node {i} p1 l-rank p1≥p l1 r1)
  (node {j} p2 r-rank p2≥p l2 r2)
  with order p1 p2
merge .{↑ i} .{↑ j}
  (node {i} p1 l-rank p1≥p l1 r1)
  (node {j} p2 r-rank p2≥p l2 r2)
  | le p1≤p2
  = makeT p1 p1≥p l1 (merge {i} {↑ j} r1 (node p2 r-rank p1≤p2 l2 r2))
merge .{↑ i} .{↑ j}
  (node {i} p1 l-rank p1≥p l1 r1)
  (node {j} p2 r-rank p2≥p l2 r2)
  | ge p1≥p2
  = makeT p2 p2≥p l2 (merge {↑ i} {j} (node p1 l-rank p1≥p2 l1 r1) r2)

-- When writing indexed insert function we once again have to answer a
-- question of how to index input and output Heap. The easiest
-- solution is to be liberal: let us require that the input and output
-- Heap have no limitations on Priorities they can store. In other
-- words, let they be indexed by zero:
insert : Priority → Heap zero → Heap zero
insert p h = merge (singleton p) h

-- Now we can create an example heap. The only difference between this
-- heap and the heap without any proofs is that we need to explicitly
-- instantiate implicit Priority parameter of empty constructor.
heap : Heap zero
heap = insert (suc (suc zero))
      (insert (suc zero)
      (insert zero
      (insert (suc (suc (suc zero))) (empty {n = zero}))))

-- But what if we want to insert into a heap that is not indexed with
-- 0? One solution is to be liberal and ``promote'' that heap so that
-- after insertion it can store elements with any priorities:
toZero : {b : Priority} → Heap b → Heap zero
toZero empty               = empty
toZero (node p rank _ l r) = node p rank ge0 l r

insert0 : {b : Priority} → Priority → Heap b → Heap zero
insert0 p h = merge (singleton p) (toZero h)

-- But what if we actaully want to maintain bounds imposed on the heap
-- by its index? To achieve that we need a new singleton function that
-- constructs a singleton Heap with a bound equal to priority of a
-- single element stored by the heap. To construct a proof required by
-- node we use ≥sym, which proves that if p ≡ p then p ≥ p.
singletonB : (p : Priority) → Heap p
singletonB p = node p one (≥sym refl) empty empty

-- We can now write new insert function that uses singletonB function:
insertB : (p : Priority) → Heap p → Heap p
insertB p h = merge (singletonB p) h
-- However, that function is pretty much useless - it can insert
-- element with priority p only to a heap that has p as its bound. In
-- other words if we have Heap zero - ie. a heap that can store any
-- possible priority -- the only thing that we can insert into it
-- using insertB function is zero. That's clearly not what we want. We
-- need a way to manipulate resulting priority bound.

-- Let's try again. This time we will write functions with signatures:
--
--  singletonB' : {b : Priority} → (p : Priority) → p ≥ b → Heap b
--  insertB' : {b : Priority} → (p : Priority) → p ≥ b → Heap p → Heap b
--
-- Singleton allows to construct Heap containing priority p but
-- bounded by b. This of course requires proof that p ≥ b, ie. that
-- priority p can actually be stored in Heap b. insertB' is similar -
-- it can insert element of priority p into Heap bounded by p but the
-- resulting Heap can be bounded by b (provided that p ≥ b, for which
-- we must supply evidence). Let's implement that.

-- Implementing singletonB' is straightforward:
singletonB' : {b : Priority} → (p : Priority) → p ≥ b → Heap b
singletonB' p p≥b = node p one p≥b empty empty

-- To implement insertB' we need two additional functions. Firstly, we
-- need a proof of transitivity of ≥. We proceed by induction on
-- c. Our base case is:
--
--   a ≥ b ∧ b ≥ 0 ⇒ a ≥ 0
--
-- In other words if c is 0 then ge0 proves the property. If c is not
-- zero, then b is also not zero (by definitions of data constructors
-- of ≥) and hence a is also not zero. This gives us second equation
-- that is a recursive proof on ≥trans.
≥trans : {a b c : Nat} → a ≥ b → b ≥ c → a ≥ c
≥trans a≥b        ge0      = ge0
≥trans (geS a≥b) (geS b≥c) = geS (≥trans a≥b b≥c)

-- Having proved the transitivity of ≥ we can construct a function
-- that loosens the bound we put on a heap. If we have a heap with a
-- bound p - meaning that all priorities in a heap are guaranteed to
-- be lower than or equal to p - and we also have evidence than n is a
-- priority higher than p then we can change the restriction on the
-- heap so that it accepts higher priorites. For example if we have
-- Heap 5, ie. all elements in the heap are 5 or greater, and we have
-- evidence that 5 ≥ 3, then we can convert Heap 5 to Heap 3. Note how
-- we are prevented from writing wrong code: if we have Heap 3 we
-- cannot convert it to Heap 5. This is not possible from theoretical
-- point of view: Heap 3 may contain 4, but Heap 5 is expected to
-- contain elements not smaller than 5. It is also not possible
-- practically: thanks to our definition of ≥ we can't orivide
-- evidence that 3 ≥ 5 because we cannot construct value of that type.
liftBound : {p b : Priority} → b ≥ p → Heap b → Heap p
liftBound b≥n empty = empty
liftBound b≥n (node p rank p≥b l r)
  = node p rank (≥trans p≥b b≥n) l r

-- With singletonB and liftBound we can construct insert function that
-- allows to insert element with priority p into a Heap bound by b,
-- but only if we can supply evidence that p ≥ b, ie. that p can
-- actually be stored in the heap.
insertB' : {b : Priority} → (p : Priority) → p ≥ b → Heap p → Heap b
insertB' p p≥b h = merge (singletonB' p p≥b) (liftBound p≥b h)

-- But if we try to create an example Heap as we did previously we
-- quickly discover that this function isn't of much use either:
heap' : Heap zero
heap' = insertB' (suc (suc zero)) {!!}
       (insertB' (suc zero) {!!}
       (insertB' zero {!!}
       (insertB' (suc (suc (suc zero))) {!!} (empty))))

-- In third hole we are required to supply evidence that 0 ≥ 1 and
-- that is not possible. The reason is that our insertB' function
-- allows us only to insert elements into a heap in decreasing order:
heap'' : Heap zero
heap'' = insertB' zero ge0
        (insertB' (suc zero) ge0
        (insertB' (suc (suc zero)) (geS ge0)
        (insertB' (suc (suc (suc zero))) (geS (geS ge0)) (empty))))
-- This is a direct consequence of our requirement that priority of
-- element being inserted and bound on the Heap we insert into match.

-- Again, findMin and deletMin are incomplete
findMin : {b : Priority} → Heap b → Priority
findMin empty            = {!!}
findMin (node p _ _ _ _) = p

-- deleteMin requires a bit more work than previously. First, notice
-- that the bound placed on the input and output heaps is the
-- same. This happens because relation between priorities in a node
-- and it's children is ≥, not > (ie. equality is allowed). We cannot
-- therefore guearantee that bound on priority will increase after
-- removing highest-priority element from the Heap. When we merge
-- left and right subtrees we need to lift their bounds so they are
-- now both b (not p).
deleteMin : {b : Priority} → Heap b → Heap b
deleteMin empty                 = {!!}
deleteMin (node p rank p≥b l r) = merge (liftBound p≥b l) (liftBound p≥b r)
