----------------------------------------------------------------------
-- Copyright: 2013, Jan Stolarek, Lodz University of Technology     --
--                                                                  --
-- License: See LICENSE file in root of the repo                    --
-- Repo address: https://github.com/jstolarek/dep-typed-wbl-heaps   --
--                                                                  --
-- Dependently-typed implementation of weight-biased leftist heap.  --
-- One-pass merging algorithm with the auxiliary function inlined   --
-- (see Okasaki, Exercise 3.4.c, p. 20).                            --
-- Work in progress.                                                --
----------------------------------------------------------------------

module NoMakeT.RankProof where

open import Basics
open import MakeT.RankProof using    ( makeT-lemma )
                            renaming ( proof-1 to proof-1a; proof-2 to proof-2a )

-- Definition same as previously
data Heap : Nat → Set where
  empty : Heap zero
  node  : {l r : Nat} → l ≥ r → Priority → Heap l → Heap r → Heap (suc (l + r))


-- Note [merge, proof 2]
-- ~~~~~~~~~~~~~~~~~~~~~
--
-- We have p1 < p2 and r1 + h2 ≥ l1. We keep p1 as the root but switch
-- the subtrees: l1 becomes new right subtree (since it is smaller)
-- and r1 merged with h2 becomes new left subtree.
--
-- (node l1≤r1+h2 p1 x1 (merge r1 (node l2ger2 p2 x2 l2 r2)) l1)
--  |                          |   |                         |
--  |    +---------------------+   |                         |
--  |    |     +-------------------+                         |
--  |    |     |               +-----------------------------+
--  |    |     |               |
-- suc ((r1 + suc (l2 + r2)) + l1)
--
-- Hence we have to prove:
--
--   suc ((r1 + suc (l2 + r2)) + l1) ≡ suc ((l1 + r1) + suc (l2 + r2))
--
-- Again we use cong to deal with the outer calls to suc, substitute
-- a = l1, b = r1 and c = suc (l2 + r2), which leaves us with a proof
-- of lemma 1:
--
--   (b + c) + a ≡ (a + b) + c
--
-- From commutativity of addition we have:
--
--   (b + c) + a ≡ a + (b + c)
--
-- and from associativity we have:
--
--   a + (b + c) ≡ (a + b) + c
--
-- We combine these two proofs with transitivity to get our final proof.

--proof-1 : (l1 r1 l2 r2 : Nat) → suc ( l1 + (r1 + suc (l2 + r2)))
--                              ≡ suc ((l1 + r1) + suc (l2 + r2))
--proof-1 l1 r1 l2 r2 = cong suc (+assoc l1 r1 (suc (l2 + r2)))

proof-1b : (l1 r1 l2 r2 : Nat) → suc ((r1 + suc (l2 + r2)) + l1)
                               ≡ suc ((l1 + r1) + suc (l2 + r2))
proof-1b l1 r1 l2 r2 = trans (makeT-lemma (r1 + suc (l2 + r2)) l1)
                             (proof-1a l1 r1 l2 r2)

lemma-B : (a b c : Nat) → (a + suc b) + c ≡ b + suc (c + a)
lemma-B a b c = trans (sym ((cong (λ n → n + c) (+suc a b))))
                (trans (cong suc
                (trans (cong (λ n → n + c) (+comm a b))
                (trans (sym (+assoc b a c)) (cong (λ n → b + n) (+comm a c))))) (+suc b (c + a)))

-- This:   sym ((cong (λ n → n + c) (+suc a b)))
-- proves: (a + suc b) + c ≡ suc ((a + b) + c)

-- This:   (three trans)
-- proves: suc (a + b) + c ≡ suc (b + (c + a))
-- where
--    this:   cong (λ n → n + c) (+comm a b)
--    proves: (a + b) + c ≡ (b + a) + c
--
--    this:   +assoc b a c
--    proves: (b + c) + a ≡ b + (c + a)
--
--    this:   cong (λ n → b + n) (+comm a c)
--    proves: b + (a + c) ≡ b + (c + a)

-- This:   +suc b (c + a)
-- proves: suc (b + (c + a)) ≡ b + suc (c + a)

--proof-2b : (l1 r1 l2 r2 : Nat) → suc ((r2 + suc (l1 + r1)) + l2) ≡ suc ((l1 + r1) + suc (l2 + r2))
--proof-2b l1 r1 l2 r2 = cong suc (lemma-B r2 (l1 + r1) l2)

proof-2b : (l1 r1 l2 r2 : Nat) → suc ((r2 + suc (l1 + r1)) + l2)
                               ≡ suc ((l1 + r1) + suc (l2 + r2))
proof-2b l1 r1 l2 r2 = trans (makeT-lemma (r2 + suc (l1 + r1)) l2)
                             (proof-2a l1 r1 l2 r2)

merge : {l r : Nat} → Heap l → Heap r → Heap (l + r)
merge {zero} {_}     empty h2 = h2
merge {suc l} {zero} h1 empty = subst Heap (sym (+0 (suc l))) h1
merge {suc .(l1-rank + r1-rank)} {suc .(l2-rank + r2-rank)}
  (node {l1-rank} {r1-rank} l1≥r1 p1 l1 r1)
  (node {l2-rank} {r2-rank} l2≥r2 p2 l2 r2)
  with p1 < p2
  | order l1-rank (r1-rank + suc (l2-rank + r2-rank))
  | order l2-rank (r2-rank + suc (l1-rank + r1-rank))
merge {suc .(l1-rank + r1-rank)} {suc .(l2-rank + r2-rank)}
  (node {l1-rank} {r1-rank} l1≥r1 p1 l1 r1)
  (node {l2-rank} {r2-rank} l2≥r2 p2 l2 r2)
  | true
  | ge l1≥r1+h2
  | _
  = subst Heap
          (proof-1a l1-rank r1-rank l2-rank r2-rank) -- See [merge, proof 1a]
          (node l1≥r1+h2 p1 l1 (merge r1 (node l2≥r2 p2 l2 r2)))
merge {suc .(l1-rank + r1-rank)} {suc .(l2-rank + r2-rank)}
  (node {l1-rank} {r1-rank} l1≥r1 p1 l1 r1)
  (node {l2-rank} {r2-rank} l2≥r2 p2 l2 r2)
  | true
  | le l1≤r1+h2
  | _
  = subst Heap
          (proof-1b l1-rank r1-rank l2-rank r2-rank) -- See [merge, proof 1b]
          (node l1≤r1+h2 p1 (merge r1 (node l2≥r2 p2 l2 r2)) l1)
merge {suc .(l1-rank + r1-rank)} {suc .(l2-rank + r2-rank)}
  (node {l1-rank} {r1-rank} l1≥r1 p1 l1 r1)
  (node {l2-rank} {r2-rank} l2≥r2 p2 l2 r2)
  | false
  | _
  | ge l2≥r2+h1
  = subst Heap
          (proof-2a l1-rank r1-rank l2-rank r2-rank) -- See [merge, proof 2a]
          (node l2≥r2+h1 p2 l2 (merge r2 (node l1≥r1 p1 l1 r1)))
merge {suc .(l1-rank + r1-rank)} {suc .(l2-rank + r2-rank)}
  (node {l1-rank} {r1-rank} l1≥r1 p1 l1 r1)
  (node {l2-rank} {r2-rank} l2≥r2 p2 l2 r2)
  | false
  | _
  | le l2≤r2+h1
  = subst Heap
          (proof-2b l1-rank r1-rank l2-rank r2-rank) -- See [merge, proof 2b]
          (node l2≤r2+h1 p2 (merge r2 (node l1≥r1 p1 l1 r1)) l2)
