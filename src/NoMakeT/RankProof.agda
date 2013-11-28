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

Priority : Set
Priority = Nat

-- Definition same as previously
data Heap (A : Set) : Nat → Set where
  empty : Heap A zero
  node  : {l r : Nat} → l ≥ r → Priority → A → Heap A l → Heap A r → Heap A (suc (l + r))

isEmpty : {A : Set} {n : Nat} → Heap A n → Bool
isEmpty empty            = true
isEmpty (node _ _ _ _ _) = false

singleton : {A : Set} → Priority → A → Heap A (suc zero)
singleton p x = node ge0 p x empty empty

-- Note [Notation for proving heap merge]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
-- In the proofs of heap merge we will use following notation:
--
--  h1, h2 - rank of heaps being merged
--  p1, p2 - priority of root element
--  l1     - rank of left subtree in the first heap
--  r1     - rank of right subtree in the first heap
--  l2     - rank of left subtree in the second heap
--  r2     - rank of right subtree in the second heap
--
-- Note that:
--
--    h1 = suc (l1 + r1)
--    h2 = suc (l2 + r2)
--
--     h1         h2
--
--     p1         p2
--    /  \       /  \
--   /    \     /    \
--  l1    r1   l2    r2


-- Note [Merging algorithm]
-- ~~~~~~~~~~~~~~~~~~~~~~~~
--
-- In all four cases we have to prove that recursive call to merge
-- produces heap of required size, which is h1 + h2. Since in the
-- proofs we always operate on l1, r1, l2 and r2 we have:
--
--   h1 + h2 ̄≡ suc (l1 + r1) + suc (l2 + r2)
--           ≡ suc ((l1 + r1) + suc (l2 + r2))
--
-- Second transformation comes from definition of _+_

-- Note [merge, proof 1]
-- ~~~~~~~~~~~~~~~~~~~~~
--
-- We have p1 < p2 and l1 ≥ r1 + h2. We keep p1 as the root and l1 as
-- its left child and need to prove that merging r2 with h2 gives
-- correct size:
--
-- node l1≥r1+h2 p1 x1 l1 (merge r1 (node l2ger2 p2 x2 l2 r2))
--  |                      |         |    |
--  |   +------------------+         |    |
--  |   |     +----------------------+    |
--  |   |     |     +---------------------+
--  |   |     |     |
-- suc (l1 + (r1 + suc (l2 + r2)))
--
-- Formally:
--
--   suc (l1 + (r1 + suc (l2 + r2))) ≡ suc ((l1 + r1) + suc (l2 + r2))
--
-- We write
--
--   cong suc X
--
-- where X proves
--
--   l1 + (r1 + suc (l2 + r2)) ≡ (l1 + r1) + suc (l2 + r2)
--
-- Substituting a = l1, b = r1 and c = suc (l2 + r2) we have
--
--   a + (b + c) ≡ (a + b) + c
--
-- Which is associativity that we have already proved.

proof-1 : (l1 r1 l2 r2 : Nat) → suc ( l1 + (r1 + suc (l2 + r2)))
                              ≡ suc ((l1 + r1) + suc (l2 + r2))
proof-1 l1 r1 l2 r2 = cong suc (+assoc l1 r1 (suc (l2 + r2)))

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

lemma-1 : (a b c : Nat) → (b + c) + a ≡ (a + b) + c
lemma-1 a b c = trans (+comm (b + c) a) (+assoc a b c)

proof-2 : (l1 r1 l2 r2 : Nat) → suc ((r1 + suc (l2 + r2)) + l1) ≡ suc ((l1 + r1) + suc (l2 + r2))
proof-2 l1 r1 l2 r2 = cong suc (lemma-1 l1 r1 (suc (l2 + r2)))

-- Inlining lemma-1 into proof-2 gives:
--
-- proof-2a : (l1 r1 l2 r2 : Nat) → suc ((r1 + suc (l2 + r2)) + l1)
--                                ≡ suc ((l1 + r1) + suc (l2 + r2))
-- proof-2a l1 r1 l2 r2 = cong suc (trans (+comm (r1 + (suc (l2 + r2))) l1)
--                                        (+assoc l1 r1 (suc (l2 + r2))))

lemma-2 : (a b : Nat) → a + suc b ≡ b + suc a
lemma-2 a b = trans (sym (+suc a b)) (trans (cong suc (+comm a b)) (+suc b a))

lemma-3 : (a b c : Nat) → a + (b + suc c) ≡ c + suc (a + b)
lemma-3 a b c = trans (+assoc a b (suc c)) (lemma-2 (a + b) c)

proof-3 : (l1 r1 l2 r2 : Nat) → suc (l2 + (r2 + suc (l1 + r1))) ≡ suc ((l1 + r1) + suc (l2 + r2))
proof-3 l1 r1 l2 r2 = cong suc (lemma-3 l2 r2 (l1 + r1))

lemma-4 : (a b c : Nat) → (a + suc b) + c ≡ b + suc (c + a)
lemma-4 a b c = trans (sym ((cong (λ n → n + c) (+suc a b))))
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

proof-4 : (l1 r1 l2 r2 : Nat) → suc ((r2 + suc (l1 + r1)) + l2) ≡ suc ((l1 + r1) + suc (l2 + r2))
proof-4 l1 r1 l2 r2 = cong suc (lemma-4 r2 (l1 + r1) l2)

-- we can combine proof of makeT with proof of 3:
proof-4a : (l1 r1 l2 r2 : Nat) → suc ((r2 + suc (l1 + r1)) + l2) ≡ suc ((l1 + r1) + suc (l2 + r2))
proof-4a l1 r1 l2 r2 = cong suc (trans (+comm ((r2 + suc (l1 + r1))) l2) (lemma-3 l2 r2 (l1 + r1)))

-- Note [Notation in merge]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
-- merge uses different notation than the proofs. We use l1, r1,
-- l2 and r2 to denote the respective subtrees and l1-rank, r1-rank,
-- l2-rank and r2-rank to denote their ranks.

merge : {A : Set} {l r : Nat} → Heap A l → Heap A r → Heap A (l + r)
merge h1 h2 with h1 | h2
merge {A} {zero} {_} h1 h2
          | empty
          | _
          = h2
merge {A} {suc l} {zero} h1 h2
          | _
          | empty
          = subst (Heap A) (sym (+0 (suc l))) h1
merge {A} {suc .(l1-rank + r1-rank)} {suc .(l2-rank + r2-rank)}
          h1 h2
          | node {l1-rank} {r1-rank} l1ger1 p1 x1 l1 r1
          | node {l2-rank} {r2-rank} l2ger2 p2 x2 l2 r2
          with p1 < p2
          | order l1-rank (r1-rank + suc (l2-rank + r2-rank))
          | order l2-rank (r2-rank + suc (l1-rank + r1-rank))
merge {A} {suc .(l1-rank + r1-rank)} {suc .(l2-rank + r2-rank)}
          h1 h2
          | node {l1-rank} {r1-rank} l1ger1 p1 x1 l1 r1
          | node {l2-rank} {r2-rank} l2ger2 p2 x2 l2 r2
          | true
          | ge l1≥r1+h2
          | _
          = subst (Heap A)
                  (proof-1 l1-rank r1-rank l2-rank r2-rank) -- See [merge, proof 1]
                  (node l1≥r1+h2 p1 x1 l1 (merge r1 h2))
merge {A} {suc .(l1-rank + r1-rank)} {suc .(l2-rank + r2-rank)}
          h1 h2
          | node {l1-rank} {r1-rank} l1ger1 p1 x1 l1 r1
          | node {l2-rank} {r2-rank} l2ger2 p2 x2 l2 r2
          | true
          | le l1≤r1+h2
          | _
          = subst (Heap A)
                  (proof-2 l1-rank r1-rank l2-rank r2-rank) -- See [merge, proof 2]
                  (node l1≤r1+h2 p1 x1 (merge r1 h2) l1)
merge {A} {suc .(l1-rank + r1-rank)} {suc .(l2-rank + r2-rank)}
          h1 h2
          | node {l1-rank} {r1-rank} l1ger1 p1 x1 l1 r1
          | node {l2-rank} {r2-rank} l2ger2 p2 x2 l2 r2
          | false
          | _
          | ge l2≥r2+h1
          = subst (Heap A)
                  (proof-3 l1-rank r1-rank l2-rank r2-rank) -- See [merge, proof 3]
                  (node l2≥r2+h1 p2 x2 l2 (merge r2 h1))
merge {A} {suc .(l1-rank + r1-rank)} {suc .(l2-rank + r2-rank)}
          h1 h2
          | (node {l1-rank} {r1-rank} l1ger1 p1 x1 l1 r1)
          | (node {l2-rank} {r2-rank} l2ger2 p2 x2 l2 r2)
          | false
          | _
          | le l2≤r2+h1
          = subst (Heap A)
                  (proof-4 l1-rank r1-rank l2-rank r2-rank) -- See [merge, proof 4]
                  (node l2≤r2+h1 p2 x2 (merge r2 h1) l2)

insert : {A : Set} {n : Nat} → Priority → A → Heap A n → Heap A (suc n)
insert p x h = merge (singleton p x) h

findMin : {A : Set} {n : Nat} → Heap A (suc n) → A
findMin (node _ _ x _ _) = x

deleteMin : {A : Set} {n : Nat} → Heap A (suc n) → Heap A n
deleteMin (node _ _ _ l r) = merge l r
