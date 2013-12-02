----------------------------------------------------------------------
-- Copyright: 2013, Jan Stolarek, Lodz University of Technology     --
--                                                                  --
-- License: See LICENSE file in root of the repo                    --
-- Repo address: https://github.com/jstolarek/dep-typed-wbl-heaps   --
--                                                                  --
-- Weight biased leftist heap that proves rank invariant: size of   --
-- left subtree of a node is not smaller than size of right         --
-- subtree.                                                         --
----------------------------------------------------------------------

module MakeT.RankProof where

open import Basics

-- We use dependent types to index a tree by its size, instead of
-- explicitly storing the size in the node constructor. Size of a tree
-- equals size of its children plus one. Additionally we store
-- evidence that a tree represents correct weight-biased leftist heap
-- i.e. that size of left subtree is at least as large as size of the
-- right one.
data Heap : Nat → Set where
  empty : Heap zero
  node  : {l r : Nat} → Priority → l ≥ r → Heap l → Heap r → Heap (suc (l + r))

singleton : Priority  → Heap (suc zero)
singleton p = node p ge0 empty empty

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
--
-- This means our proof is two-stage. We need to prove that
--
--  1) makeT produces node of required size, even if it swaps left
--     and right children.
--
--  2) recursive calls to merge produce trees of required size.

-- Note [Proving makeT]
-- ~~~~~~~~~~~~~~~~~~~~
--
-- makeT has two cases:
--
--  1) size of l is ≥ than size of r in which case no extra
--     proof is necessary.
--
--  2) size of r is ≥ than size of l in which case we swap left and
--     right subtrees. This requires us to prove that:
--
--       suc (r + l) ≡ suc (l + r)
--
--     That proof is done using congruence on suc function and
--     commutativity of addition.

makeT : {l r : Nat} → Priority → Heap l → Heap r → Heap (suc (l + r))
makeT {l-rank} {r-rank} p l r with order l-rank r-rank
makeT {l-rank} {r-rank} p l r | ge l≥r
  = node p l≥r l r
makeT {l-rank} {r-rank} p l r | le r≥l
  = subst Heap (cong suc (+comm r-rank l-rank)) (node p r≥l r l)

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


-- Note [Proving merge]
-- ~~~~~~~~~~~~~~~~~~~~
--
-- We need to proove that all four cases of merge (see [Merging
-- algorithm]) produce heap of required size, which is h1 + h2. Since in
-- the proofs we always operate on l1, r1, l2 and r2 we have:
--
--   h1 + h2 ̄≡ suc (l1 + r1) + suc (l2 + r2)
--           ≡ suc ((l1 + r1) + suc (l2 + r2))
--
-- (Second transformation comes from definition of _+_)


-- Note [merge, proof 0a]
-- ~~~~~~~~~~~~~~~~~~~~~~
--
-- h1 ≡ 0, therefore: h1 + h2 ≡ 0 + h2 ≡ h2 ∎
--
-- This is definitional equality based on _+_
--
-- ∎

-- Note [merge, proof 0b]
-- ~~~~~~~~~~~~~~~~~~~~~~
--
-- h2 ≡ 0, therefore expected size is h1 + h2 ≡ h1 + 0. We need to
-- show that:
--
--    h1 ≡ h1 + 0
--
-- We use proof of the fact that 0 is right identity of addition. Sice
-- our proof is done in the opposite direction we must additionally
-- use symmetry.
--
-- ∎

-- Note [merge, proof 1]
-- ~~~~~~~~~~~~~~~~~~~~~
--
-- We have p1 < p2. We keep p1 as the root and need to prove that
-- merging r1 with h2 gives correct size:
--
--   makeT p1 x1 l1 (merge r1 h2)
--    |          |     |
--    |   +------+     |
--    |   |     _______|__________
--    |   |    /                  \
--   suc (l1 + (r1 + suc (l2 + r2)))
--                   \___________/
--                         h2
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
--
-- ∎

proof-1 : (l1 r1 l2 r2 : Nat) → suc ( l1 + (r1 + suc (l2 + r2)))
                              ≡ suc ((l1 + r1) + suc (l2 + r2))
proof-1 l1 r1 l2 r2 = cong suc (+assoc l1 r1 (suc (l2 + r2)))

-- Note [merge, proof 2]
-- ~~~~~~~~~~~~~~~~~~~~~
--
-- We have p2 < p1. We keep p2 as the root and need to prove that
-- merging r2 with h1 gives correct size:
--
--   makeT p2 x2 l2 (merge r2 h1)
--    |          |     |
--    |   +------+     |
--    |   |     _______|__________
--    |   |    /                  \
--   suc (l2 + (r2 + suc (l1 + r1)))
--                    \__________/
--                         h1
-- Formally:
--
--   suc (l2 + (r2 + suc (l1 + r1))) ≡ suc ((l1 + r1) + suc (l2 + r2))
--
-- Again we use cong to deal with the outer calls to suc, substitute
-- a = l2, b = r2 and c = l1 + r1), which leaves us with a proof
-- of lemma B:
--
--   a + (b + suc c) ≡ c + suc (a + b)
--
-- From associativity we know that:
--
--   a + (b + suc c) ≡ (a + b) + suc c
--
-- If we prove lemma A:
--
--  (a + b) + suc c = c + suc (a + b)
--
-- we can combine it using transitivity to get the final proof. We can
-- rewrite lemma A as:
--
--    n + suc m ≡ m + suc n
--
-- where n = a + b and m = c. We start by using symmetry on +suc:
---
--   n + (suc m) ≡ suc (n + m)
--
-- Using transitivity we combine it with congruence on commutativity
-- of addition to prove:
--
--   suc (n + m) ≡ suc (m + n)
--
-- Again, using transitivity we combine it with +suc:
--
--   suc (m + n) ≡ m + suc n
--
-- ∎

lemma-A : (n m : Nat) → n + suc m ≡ m + suc n
lemma-A n m = trans (sym (+suc n m)) (trans (cong suc (+comm n m)) (+suc m n))

lemma-B : (a b c : Nat) → a + (b + suc c) ≡ c + suc (a + b)
lemma-B a b c = trans (+assoc a b (suc c)) (lemma-A (a + b) c)

proof-2 : (l1 r1 l2 r2 : Nat) → suc (l2 + (r2  + suc (l1 + r1)))
                              ≡ suc ((l1 + r1) + suc (l2 + r2))
proof-2 l1 r1 l2 r2 = cong suc (lemma-B l2 r2 (l1 + r1))

-- Inlining lemmas A and B into proof-2 gives:
--
--   proof-2a : (l1 r1 l2 r2 : Nat) → suc (l2 + (r2  + suc (l1 + r1)))
--                                 ≡ suc ((l1 + r1) + suc (l2 + r2))
--   proof-2a l1 r1 l2 r2 =
--     cong suc (trans (+assoc l2 r2 (suc (l1 + r1)))
--              (trans (sym (+suc (l2 + r2) (l1 + r1)))
--              (trans (cong suc (+comm (l2 + r2) (l1 + r1)))
--                     (+suc (l1 + r1) (l2 + r2))))


-- Note [Notation in merge]
-- ~~~~~~~~~~~~~~~~~~~~~~~~
--
-- merge uses different notation than the proofs. We use l1, r1, l2
-- and r2 to denote the respective subtrees and l1-rank, r1-rank,
-- l2-rank and r2-rank to denote their ranks. We use h1 and h2 to
-- denote heaps.

merge : {l r : Nat} → Heap l → Heap r → Heap (l + r)
merge h1 h2 with h1 | h2
merge {zero} {_} h1 h2
          | empty
          | _
          = h2 -- See [merge, proof 0a]
merge {suc l} {zero} h1 h2
          | _
          | empty
          = subst Heap
                  (sym (+0 (suc l)))  -- See [merge, proof 0b]
                  h1
merge {suc .(l1-rank + r1-rank)} {suc .(l2-rank + r2-rank)}
          h1 h2
          | node {l1-rank} {r1-rank} p1 l1≥r1 l1 r1
          | node {l2-rank} {r2-rank} p2 l2≥r2 l2 r2
          with p1 < p2
merge {suc .(l1-rank + r1-rank)} {suc .(l2-rank + r2-rank)}
          h1 h2
          | node {l1-rank} {r1-rank} p1 l1≥r1 l1 r1
          | node {l2-rank} {r2-rank} p2 l2≥r2 l2 r2
          | true
          = subst Heap
                  (proof-1 l1-rank r1-rank l2-rank r2-rank) -- See [merge, proof 1]
                  (makeT p1 l1 (merge r1 h2))
merge {suc .(l1-rank + r1-rank)} {suc .(l2-rank + r2-rank)}
          h1 h2
          | node {l1-rank} {r1-rank} p1 l1≥r1 l1 r1
          | node {l2-rank} {r2-rank} p2 l2≥r2 l2 r2
          | false
          = subst Heap
                  (proof-2 l1-rank r1-rank l2-rank r2-rank) -- See [merge, proof 2]
                  (makeT p2 l2 (merge r2 h1))

insert : {n : Nat} → Priority → Heap n → Heap (suc n)
insert p h = merge (singleton p) h

findMin : {n : Nat} → Heap (suc n) → Priority
findMin (node p _ _ _) = p

deleteMin : {n : Nat} → Heap (suc n) → Heap n
deleteMin (node _ _ l r) = merge l r
