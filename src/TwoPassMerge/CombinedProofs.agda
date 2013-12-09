----------------------------------------------------------------------
-- Copyright: 2013, Jan Stolarek, Lodz University of Technology     --
--                                                                  --
-- License: See LICENSE file in root of the repo                    --
-- Repo address: https://github.com/jstolarek/dep-typed-wbl-heaps   --
--                                                                  --
-- Weight biased leftist tree that proves both priority and rank    --
-- invariants. Uses a two-pass merging algorithm.                   --
----------------------------------------------------------------------

{-# OPTIONS --sized-types #-}
module TwoPassMerge.CombinedProofs where

open import Basics
open import Sized
open import TwoPassMerge.RankProof using ( makeT-lemma; proof-1; proof-2 )

-- Now that we have separate proofs of priority and rank invariants we
-- can combine them into one proof. We index Heap with two indices:
-- one for Priority and one for Rank.
data Heap : {i : Size} → Priority → Rank → Set where
  empty : {i : Size} {b : Priority} → Heap {↑ i} b zero
  node  : {i : Size} {b : Priority} → (p : Priority) → p ≥ b → {l r : Rank} →
          l ≥ r → Heap {i} p l → Heap {i} p r → Heap {↑ i} b (suc (l + r))

-- Now we will combine functions that prove priority invariant and
-- functions that prove rank invariant into functions that prove both
-- invariants.

-- Let's begin with singleton. Note the type of created Heap. We set
-- first index to zero, because it proves the priority invariant and
-- second index to one because it proves rank invariant. The node now
-- needs two ge0 evidence.
singleton : Priority → Heap zero one
singleton p = node p ge0 ge0 empty empty

-- makeT function requires that we supply evidence that priority
-- invariant holds (value of type p ≥ b), guarantees that resulting
-- heap has correct size and maintains rank invariant by using Order
-- type to supply evidence of rank correctness to node constructor.
makeT : {b : Priority} {l r : Rank} → (p : Priority) → p ≥ b →
      Heap p l → Heap p r → Heap b (suc (l + r))
makeT {b} {l-rank} {r-rank} p p≥n l r with order l-rank r-rank
makeT {b} {l-rank} {r-rank} p p≥n l r | ge l≥r
  = node p p≥n l≥r l r
makeT {b} {l-rank} {r-rank} p p≥n l r | le r≥l
  = subst (Heap b) (makeT-lemma r-rank l-rank) (node p p≥n r≥l r l)

-- merge combines previous proofs:
--
--  1) it enforces priority invariant by comparing priorities using
--     order function. Recall that this function returns value of
--     Order datatype that not only gives a result of comparison but
--     also supplies evidence that result is true. That evidence is
--     given to makeT which uses it to construct a new node.
--
--  2) it proves size invariant of merge by reusing proofs from
--     TwoPassMerge.RankProof
--
--  3) it delegates the proof of rank invariant to makeT
merge : {i j : Size} {b : Priority} {l r : Rank} → Heap {i} b l → Heap {j} b r
      → Heap b (l + r)
merge empty h2 = h2 -- See [merge, proof 0a]
merge {_} .{_} {b} {suc l} {zero} h1 empty
  = subst (Heap b)
          (sym (+0 (suc l)))  -- See [merge, proof 0b]
          h1
merge .{↑ i} .{↑ j} .{b} {suc .(l1-rank + r1-rank)} {suc .(l2-rank + r2-rank)}
  (node {i} .{b} p1 p1≥b {l1-rank} {r1-rank} l1≥r1 l1 r1)
  (node {j}  {b} p2 p2≥b {l2-rank} {r2-rank} l2≥r2 l2 r2)
  with order p1 p2
merge .{↑ i} .{↑ j} .{b} {suc .(l1-rank + r1-rank)} {suc .(l2-rank + r2-rank)}
  (node {i} .{b} p1 p1≥b {l1-rank} {r1-rank} l1≥r1 l1 r1)
  (node {j}  {b} p2 p2≥b {l2-rank} {r2-rank} l2≥r2 l2 r2)
  | le p1≤p2
  = subst (Heap b)
          (proof-1 l1-rank r1-rank l2-rank r2-rank) -- See [merge, proof 1]
          (makeT p1 p1≥b l1 (merge {i} {↑ j} r1 (node p2 p1≤p2 l2≥r2 l2 r2)))
merge .{↑ i} .{↑ j} .{b} {suc .(l1-rank + r1-rank)} {suc .(l2-rank + r2-rank)}
  (node {i} .{b} p1 p1≥b {l1-rank} {r1-rank} l1≥r1 l1 r1)
  (node {j}  {b} p2 p2≥b {l2-rank} {r2-rank} l2≥r2 l2 r2)
  | ge p1≥p2
  = subst (Heap b)
          (proof-2 l1-rank r1-rank l2-rank r2-rank) -- See [merge, proof 2]
          (makeT p2 p2≥b l2 (merge {j} {↑ i} r2 (node p1 p1≥p2 l1≥r1 l1 r1)))

-- Implementations of insert and findMin are the same as
-- previously. We only need to update the type signature accordingly.
insert : {b : Priority} {r : Rank} → Priority → Heap zero r → Heap zero (suc r)
insert p h = merge (singleton p) h

findMin : {b : Priority} {r : Rank} → Heap b (suc r) → Priority
findMin (node p _ _ _ _) = p

-- To define deleteMin we will need to update definition of
-- liftBound. We need to redefine ≥trans because Agda won't let us
-- import it from a module that has unfinished implementation (recall
-- that we left definitions of findMin and deleteMin incomplete in
-- TwoPassMerge.PriorityProof).
≥trans : {a b c : Nat} → a ≥ b → b ≥ c → a ≥ c
≥trans a≥b        ge0      = ge0
≥trans (geS a≥b) (geS b≥c) = geS (≥trans a≥b b≥c)

liftBound : {p b : Priority} → b ≥ p → {r : Rank} → Heap b r → Heap p r
liftBound b≥n empty                = empty
liftBound b≥n (node p p≥b l≥r l r) = node p (≥trans p≥b b≥n) l≥r l r

-- With the new definition of liftBound we can now define deleteMin.
-- Implementation is identical to the one in TwoPassMerge.RankProof -
-- we only had to update type signature.
deleteMin : {b : Priority} {r : Rank} → Heap b (suc r) → Heap b r
deleteMin (node _ p≥b _ l r) = merge (liftBound p≥b l) (liftBound p≥b r)
