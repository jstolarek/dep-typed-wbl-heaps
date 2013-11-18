----------------------------------------------------------------------
-- Copyright: 2013, Jan Stolarek, Lodz University of Technology     --
--                                                                  --
-- License: See LICENSE file in root of the repo                    --
-- Repo address: https://github.com/jstolarek/dep-typed-heaps       --
--                                                                  --
-- Dependently-typed implementation of weight-biased leftist heap.  --
-- Work in progress.                                                --
----------------------------------------------------------------------

module DepTypedWeightedHeapMakeT where

open import DepTypedBasics

--for the moment we re-invent definition of Heap. This is temporary (I hope)
record Heap (H : Set → Set) : Set1 where
  field
    empty   : ∀ {A} → H A
    isEmpty : ∀ {A} → H A → Bool

    singleton : ∀ {A} → A → H A
    merge  : ∀ {A} → H A → H A → H A
    insert : ∀ {A} → Nat → A → H A → H A

    findMin   : ∀ {A} → H A → A
    deleteMin : ∀ {A} → H A → H A
open Heap {{...}} public

-- TODO: Import Priority from Heap

Priority : Set
Priority = Nat

-- index = tree size
-- TODO: currently there is no proof that priority of node is smaller than
-- its children. Add additional index?
data WBLHeap (A : Set) : Nat → Set where
  wblhEmpty : WBLHeap A zero
  wblhNode  : {l r : Nat} → l ≥ r → Priority → A → WBLHeap A l → WBLHeap A r → WBLHeap A (suc (l + r))

-- Now we have dependent types, so we don't need rank but we need
-- evidence that left rank is at least as large as the right one

wblhIsEmpty : {A : Set} {n : Nat} → WBLHeap A n → Bool
wblhIsEmpty wblhEmpty            = true
wblhIsEmpty (wblhNode _ _ _ _ _) = false

wblhSingleton : {A : Set} → Priority → A → WBLHeap A (suc zero)
wblhSingleton p x = wblhNode ge0 p x wblhEmpty wblhEmpty

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

-- Note [wblhMerge, proof 1]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~
--
-- We have p1 < p2 and l1 ≥ r1 + h2. We keep p1 as the root and l1 as
-- its left child and need to prove that merging r2 with h2 gives
-- correct size:
--
-- wblhNode l1≥r1+h2 p1 x1 l1 (wblhMerge r1 (wblhNode l2ger2 p2 x2 l2 r2))
--  |                      |             |    |
--  |   +------------------+             |    |
--  |   |     +--------------------------+    |
--  |   |     |     +-------------------------+
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

proof-1 : (l1 r1 l2 r2 : Nat) → suc (l1 + (r1 + suc (l2 + r2))) ≡ suc ((l1 + r1) + suc (l2 + r2))
proof-1 l1 r1 l2 r2 = cong suc (+assoc l1 r1 (suc (l2 + r2)))

lemma-2 : (a b : Nat) → a + suc b ≡ b + suc a
lemma-2 a b = trans (sym (+suc a b)) (trans (cong suc (+comm a b)) (+suc b a))

lemma-3 : (a b c : Nat) → a + (b + suc c) ≡ c + suc (a + b)
lemma-3 a b c = trans (+assoc a b (suc c)) (lemma-2 (a + b) c)

proof-3 : (l1 r1 l2 r2 : Nat) → suc (l2 + (r2 + suc (l1 + r1))) ≡ suc ((l1 + r1) + suc (l2 + r2))
proof-3 l1 r1 l2 r2 = cong suc (lemma-3 l2 r2 (l1 + r1))

-- Note [Notation in wblhMerge]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
-- wblhMerge uses different notation than the proofs. We use l1, r1,
-- l2 and r2 to denote the respective subtrees and l1-rank, r1-rank,
-- l2-rank and r2-rank to denote their ranks.

wblhMakeT : {A : Set} {l r : Nat} → Priority → A → WBLHeap A l → WBLHeap A r → WBLHeap A (suc (l + r))
wblhMakeT {A} {l-rank} {r-rank} p x l r with order l-rank r-rank
wblhMakeT {A} {l-rank} {r-rank} p x l r | ge lger
  = wblhNode lger p x l r
wblhMakeT {A} {l-rank} {r-rank} p x l r | le rgel
  = subst (WBLHeap A) (cong suc (+comm r-rank l-rank)) (wblhNode rgel p x r l)

wblhMerge : {A : Set} {l r : Nat} → WBLHeap A l → WBLHeap A r → WBLHeap A (l + r)
wblhMerge h1 h2 with h1 | h2
wblhMerge {A} {zero} {_} h1 h2
          | wblhEmpty
          | _
          = h2
wblhMerge {A} {suc l} {zero} h1 h2
          | _
          | wblhEmpty
          = subst (WBLHeap A) (sym (+0 (suc l))) h1
wblhMerge {A} {suc .(l1-rank + r1-rank)} {suc .(l2-rank + r2-rank)}
          h1 h2
          | wblhNode {l1-rank} {r1-rank} l1ger1 p1 x1 l1 r1
          | wblhNode {l2-rank} {r2-rank} l2ger2 p2 x2 l2 r2
          with p1 < p2
wblhMerge {A} {suc .(l1-rank + r1-rank)} {suc .(l2-rank + r2-rank)}
          h1 h2
          | wblhNode {l1-rank} {r1-rank} l1ger1 p1 x1 l1 r1
          | wblhNode {l2-rank} {r2-rank} l2ger2 p2 x2 l2 r2
          | true
          = subst (WBLHeap A)
                  (proof-1 l1-rank r1-rank l2-rank r2-rank)
                  (wblhMakeT p1 x1 l1 (wblhMerge r1 h2))
wblhMerge {A} {suc .(l1-rank + r1-rank)} {suc .(l2-rank + r2-rank)}
          h1 h2
          | wblhNode {l1-rank} {r1-rank} l1ger1 p1 x1 l1 r1
          | wblhNode {l2-rank} {r2-rank} l2ger2 p2 x2 l2 r2
          | false
          = subst (WBLHeap A)
                  (proof-3 l1-rank r1-rank l2-rank r2-rank)
                  (wblhMakeT p2 x2 l2 (wblhMerge r2 h1))

wblhInsert : {A : Set} {n : Nat} → Priority → A → WBLHeap A n → WBLHeap A (suc n)
wblhInsert p x h = wblhMerge (wblhSingleton p x) h

wblhFindMin : {A : Set} {n : Nat} → WBLHeap A (suc n) → A
wblhFindMin (wblhNode _ _ x _ _) = x

wblhDeleteMin : {A : Set} {n : Nat} → WBLHeap A (suc n) → WBLHeap A n
wblhDeleteMin (wblhNode _ _ _ l r) = wblhMerge l r

