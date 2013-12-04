----------------------------------------------------------------------
-- Copyright: 2013, Jan Stolarek, Lodz University of Technology     --
--                                                                  --
-- License: See LICENSE file in root of the repo                    --
-- Repo address: https://github.com/jstolarek/dep-typed-wbl-heaps   --
--                                                                  --
-- Dependently-typed implementation of weight-biased leftist heap.  --
-- Two-stage heap merging algorithm using auxiliary makeT function  --
-- (see Okasaki, Chapter 3.1, pp. 17-19)                            --
----------------------------------------------------------------------

{-# OPTIONS --sized-types #-}
module MakeT.CombinedProofs where

open import Basics
open import Sized

-- We use dependent types to index a tree by its size, instead of
-- explicitly storing the size in the node constructor. Size of a tree
-- equals size of its children plus one. Additionally we store
-- evidence that a tree represents correct weight-biased leftist heap
-- i.e. that size of left subtree is at least as large as size of the
-- right one.
data Heap : {i : Size} → Nat → Nat → Set where
  empty : {i : Size} {n : Nat} → Heap {↑ i} n zero
  node  : {i : Size} {l r n : Nat} → (p : Priority) → l ≥ r → p ≥ n →
          Heap {i} p l → Heap {i} p r → Heap {↑ i} n (suc (l + r))

isEmpty : {n m : Nat} → Heap n m → Bool
isEmpty empty              = true
isEmpty (node _ _ _ _ _) = false

-- here we use liberal singleton index
singleton : Priority → Heap zero one
singleton p = node p ge0 ge0 empty empty


makeT : {l r n : Nat} → (p : Priority) → p ≥ n → Heap p l → Heap p r → Heap n (suc (l + r))
makeT {l-rank} {r-rank} {n} p p≥n l r with order l-rank r-rank
makeT {l-rank} {r-rank} {n} p p≥n l r | ge lger
  = node p lger p≥n l r
makeT {l-rank} {r-rank} {n} p p≥n l r | le rgel
  = subst (Heap n) (cong suc (+comm r-rank l-rank)) (node p rgel p≥n r l)

proof-1 : (l1 r1 l2 r2 : Nat) → suc ( l1 + (r1 + suc (l2 + r2)))
                              ≡ suc ((l1 + r1) + suc (l2 + r2))
proof-1 l1 r1 l2 r2 = cong suc (+assoc l1 r1 (suc (l2 + r2)))

lemma-A : (n m : Nat) → n + suc m ≡ m + suc n
lemma-A n m = trans (sym (+suc n m)) (trans (cong suc (+comm n m)) (+suc m n))

lemma-B : (a b c : Nat) → a + (b + suc c) ≡ c + suc (a + b)
lemma-B a b c = trans (+assoc a b (suc c)) (lemma-A (a + b) c)

proof-2 : (l1 r1 l2 r2 : Nat) → suc (l2 + (r2  + suc (l1 + r1)))
                              ≡ suc ((l1 + r1) + suc (l2 + r2))
proof-2 l1 r1 l2 r2 = cong suc (lemma-B l2 r2 (l1 + r1))

merge : {i j : Size} {l r b : Nat} → Heap {i}  b l → Heap {j} b r → Heap b (l + r)
merge empty h2 = h2 -- See [merge, proof 0a]
merge {_} .{_} {suc l} {zero} {b} h1 empty
          = subst (Heap b)
                  (sym (+0 (suc l)))  -- See [merge, proof 0b]
                  h1
merge .{↑ i} .{↑ j} {suc .(l1-rank + r1-rank)} {suc .(l2-rank + r2-rank)} {b}
          (node {i} {l1-rank} {r1-rank} p1 l1≥r1 p1≥b l1 r1)
          (node {j} {l2-rank} {r2-rank} p2 l2≥r2 p2≥b l2 r2)
          with order p1 p2
merge .{↑ i} .{↑ j} {suc .(l1-rank + r1-rank)} {suc .(l2-rank + r2-rank)} {b}
          (node {i} {l1-rank} {r1-rank} p1 l1≥r1 p1≥b l1 r1)
          (node {j} {l2-rank} {r2-rank} p2 l2≥r2 p2≥b l2 r2)
          | le p1≤p2
          = subst (Heap b)
                  (proof-1 l1-rank r1-rank l2-rank r2-rank) -- See [merge, proof 1]
                  (makeT p1 p1≥b l1 (merge {i} {↑ j} r1 (node p2 l2≥r2 p1≤p2 l2 r2)))
merge .{↑ i} .{↑ j} {suc .(l1-rank + r1-rank)} {suc .(l2-rank + r2-rank)} {b}
          (node {i} {l1-rank} {r1-rank} p1 l1≥r1 p1≥b l1 r1)
          (node {j} {l2-rank} {r2-rank} p2 l2≥r2 p2≥b l2 r2)
          | ge p1≥p2
          = subst (Heap b)
                  (proof-2 l1-rank r1-rank l2-rank r2-rank) -- See [merge, proof 2]
                  (makeT p2 p2≥b l2 (merge {j} {↑ i} r2 (node p1 l1≥r1 p1≥p2 l1 r1)))

toZero : {n b : Nat} → Heap b n → Heap zero n
toZero empty               = empty
toZero (node p rank _ l r) = node p rank ge0 l r

insert : {b n : Nat} → Priority → Heap b n → Heap zero (suc n)
insert p h = merge (singleton p) (toZero h)

findMin : {n b : Nat} → Heap b (suc n) → Priority
findMin (node p _ _ _ _) = p

deleteMin : {n b : Nat} → Heap b (suc n) → Heap zero n
deleteMin (node _ _ _ l r) = merge (toZero l) (toZero r)
