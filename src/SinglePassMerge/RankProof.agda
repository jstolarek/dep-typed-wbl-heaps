----------------------------------------------------------------------
-- Copyright: 2013, Jan Stolarek, Lodz University of Technology     --
--                                                                  --
-- License: See LICENSE file in root of the repo                    --
-- Repo address: https://github.com/jstolarek/dep-typed-wbl-heaps   --
--                                                                  --
-- Weight biased leftist heap that proves rank invariant and uses   --
-- a single-pass merging algorithm.                                 --
----------------------------------------------------------------------

module SinglePassMerge.RankProof where

open import Basics
-- We import rank proofs conducted earlier - they will be re-used.
open import TwoPassMerge.RankProof
            using    ( makeT-lemma )
            renaming ( proof-1 to proof-1a; proof-2 to proof-2a )

data Heap : Nat → Set where
  empty : Heap zero
  node  : Priority → {l r : Nat} → l ≥ r → Heap l → Heap r → Heap (suc (l + r))

-- Note [Privoving rank invariant in single-pass merge]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
-- Recall that in TwoPassMerge.RankProof we need to prove that:
--
--  1) makeT constructs node of correct size. There were two cases:
--
--     a) constructing a node without swapping l and r subtrees passed
--        to makeT. No extra proof was required as everything followed
--        from definitions.
--
--     b) constructing a node by swapping l and r subtrees (when rank
--        of r was greater than rank of l). We had to prove that:
--
--                    suc (a + b) ≡ suc (b + a)
--
--        This proof is supplied by a function makeT-lemma.
--
--  2) resulting heap produced by merge has correct size. Merge has 4
--     cases (see [Two-pass merging algorithm]):
--
--     a) h1 is empty. No extra proof required (everything follows
--        from definition of +). See [merge, proof 0a].
--
--     b) h2 is empty. We had to prove that:
--
--                 h1 ≡ h1 + 0
--
--        This proof is supplied by +0 (in Basics.Reasoning) and is
--        inlined in the definition of merge. See [merge, proof 0b].
--
--     c) priority p1 is higher than p2. We had to prove:
--
--            suc (l1 + (r1 + suc (l2 + r2)))
--                           ≡ suc ((l1 + r1) + suc (l2 + r2))
--
--        This proof is supplied by proof-1 (renamed to proof-1a in
--        this module). See [merge, proof 1] for details.
--
--     d) priority p2 is higher than p1. We had to prove:
--
--            suc (l2 + (r2  + suc (l1 + r1)))
--                           ≡ suc ((l1 + r1) + suc (l2 + r2))
--
--        This proof is supplied by proof-2 (renamed to proof-2a in
--        this module). See [merge, proof 2] for details.
--
-- Now that we inline makeT into merge and we will have to construct
-- new proofs of merge that take into account the fact that makeT has
-- been inlinined. Let's take a detailed look into the problem and
-- analyze possible solutions.
--
-- First of all let us note that we only made calls to makeT in
-- inductive cases of merge (points 2c and 2d above). This means that
-- implementation of base cases of merge (2a and 2b above) remains
-- unchanged. Let's take a look at proofs we need to supply for each
-- of four inductive cases of merge (see [Single-pass merging
-- algorithm] for description of each case):
--
--   1) case c described in [Single-pass merging algorithm]. Call to
--      makeT would not swap left and right when creating a node from
--      parameters passed to it. Required proof is:
--
--            suc (l1 + (r1 + suc (l2 + r2)))
--                           ≡ suc ((l1 + r1) + suc (l2 + r2))
--
--   2) case d described in [Single-pass merging algorithm]. Call to
--      makeT would swap left and right when creating a node from
--      parameters passed to it. Required proof is:
--
--            suc ((r1 + suc (l2 + r2)) + l1)
--                           ≡ suc ((l1 + r1) + suc (l2 + r2))
--
--   3) case e described in [Single-pass merging algorithm]. Call to
--      makeT would not swap left and right when creating a node from
--      parameters passed to it. Required proof is:
--
--            suc (l2 + (r2  + suc (l1 + r1)))
--                           ≡ suc ((l1 + r1) + suc (l2 + r2))
--
--   4) case f described in [Single-pass merging algorithm]. Call to
--      makeT would swap left and right when creating a node from
--      parameters passed to it. Required proof is:
--
--            suc ((r2 + suc (l1 + r1)) + l2)
--                           ≡ suc ((l1 + r1) + suc (l2 + r2))
--
-- First of all we must note that proofs required in cases 1 and 3 are
-- exactly the same as in the two-pass merging algorithm. This allows
-- us to re-use the old proofs (renamed to proof-1a and proof-2a
-- here). What about proofs of cases 2 and 4? One thing we could do is
-- construct proofs of these properties using technique described in
-- Note [Constructing equality proofs using transitivity]. This is
-- left as an exercise to the reader. Here we will proceed in a
-- different way. Notice that properties we have to prove in cases for
-- 2 and 4 are very similar to properties 1 and 3 (we omit the RHS
-- since it is always the same):
--
--  1: suc (l1 + (r1 + suc (l2 + r2)))
--  2: suc ((r1 + suc (l2 + r2)) + l1)
--
--  3: suc (l2 + (r2  + suc (l1 + r1)))
--  4: suc ((r2 + suc (l1 + r1)) + l2)
--
-- The only difference between 1 and 2 and between 3 and 4 is the
-- order of parameters inside outer suc. This is expected: in cases 2
-- and 4 we swap left and right subtree passed to node and this is
-- reflected in the types. Now, if we could prove that:
--
--            suc ((r1 + suc (l2 + r2)) + l1)
--                           ≡ suc (l1 + (r1 + suc (l2 + r2)))
--
-- and
--
--            suc ((r2 + suc (l1 + r1)) + l2)
--                           ≡ suc (l2 + (r2  + suc (l1 + r1)))
--
-- then we could use transitivity to combine these new proofs with old
-- proof-1a and proof-2a. If we abstract the parameters in the above
-- equalities we see that the property we need to prove is:
--
--                    suc (a + b) ≡ suc (b + a)
--
-- And that happens to be makeT-lemma! New version of merge was
-- created by inlining calls to make and now it turns out we can
-- construct proofs of that implementation by using proofs of
-- makeT. This leads us to very elegant solutions presented below.

proof-1b : (l1 r1 l2 r2 : Nat) → suc ((r1 + suc (l2 + r2)) + l1)
                               ≡ suc ((l1 + r1) + suc (l2 + r2))
proof-1b l1 r1 l2 r2 = trans (makeT-lemma (r1 + suc (l2 + r2)) l1)
                             (proof-1a l1 r1 l2 r2)

proof-2b : (l1 r1 l2 r2 : Nat) → suc ((r2 + suc (l1 + r1)) + l2)
                               ≡ suc ((l1 + r1) + suc (l2 + r2))
proof-2b l1 r1 l2 r2 = trans (makeT-lemma (r2 + suc (l1 + r1)) l2)
                             (proof-2a l1 r1 l2 r2)

-- We can now use proof-1a, proof-1b, proof-2a and proof-2b in
-- definition of merge.
merge : {l r : Nat} → Heap l → Heap r → Heap (l + r)
merge {zero} {_}     empty h2 = h2
merge {suc l} {zero} h1 empty = subst Heap (sym (+0 (suc l))) h1
merge {suc .(l1-rank + r1-rank)} {suc .(l2-rank + r2-rank)}
  (node p1 {l1-rank} {r1-rank} l1≥r1 l1 r1)
  (node p2 {l2-rank} {r2-rank} l2≥r2 l2 r2)
  with p1 < p2
  | order l1-rank (r1-rank + suc (l2-rank + r2-rank))
  | order l2-rank (r2-rank + suc (l1-rank + r1-rank))
merge {suc .(l1-rank + r1-rank)} {suc .(l2-rank + r2-rank)}
  (node p1 {l1-rank} {r1-rank} l1≥r1 l1 r1)
  (node p2 {l2-rank} {r2-rank} l2≥r2 l2 r2)
  | true
  | ge l1≥r1+h2
  | _
  = subst Heap
          (proof-1a l1-rank r1-rank l2-rank r2-rank)
          (node p1 l1≥r1+h2 l1 (merge r1 (node p2 l2≥r2 l2 r2)))
merge {suc .(l1-rank + r1-rank)} {suc .(l2-rank + r2-rank)}
  (node p1 {l1-rank} {r1-rank} l1≥r1 l1 r1)
  (node p2 {l2-rank} {r2-rank} l2≥r2 l2 r2)
  | true
  | le l1≤r1+h2
  | _
  = subst Heap
          (proof-1b l1-rank r1-rank l2-rank r2-rank)
          (node p1 l1≤r1+h2 (merge r1 (node p2 l2≥r2 l2 r2)) l1)
merge {suc .(l1-rank + r1-rank)} {suc .(l2-rank + r2-rank)}
  (node p1 {l1-rank} {r1-rank} l1≥r1 l1 r1)
  (node p2 {l2-rank} {r2-rank} l2≥r2 l2 r2)
  | false
  | _
  | ge l2≥r2+h1
  = subst Heap
          (proof-2a l1-rank r1-rank l2-rank r2-rank)
          (node p2 l2≥r2+h1 l2 (merge r2 (node p1 l1≥r1 l1 r1)))
merge {suc .(l1-rank + r1-rank)} {suc .(l2-rank + r2-rank)}
  (node p1 {l1-rank} {r1-rank} l1≥r1 l1 r1)
  (node p2 {l2-rank} {r2-rank} l2≥r2 l2 r2)
  | false
  | _
  | le l2≤r2+h1
  = subst Heap
          (proof-2b l1-rank r1-rank l2-rank r2-rank)
          (node p2 l2≤r2+h1 (merge r2 (node p1 l1≥r1 l1 r1)) l2)
