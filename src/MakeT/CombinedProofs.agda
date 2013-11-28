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

module MakeT.CombinedProofs where

open import Basics

Priority : Set
Priority = Nat

-- We use dependent types to index a tree by its size, instead of
-- explicitly storing the size in the node constructor. Size of a tree
-- equals size of its children plus one. Additionally we store
-- evidence that a tree represents correct weight-biased leftist heap
-- i.e. that size of left subtree is at least as large as size of the
-- right one.
data Heap (A : Set) : Nat → Nat → Set where
  empty : {n : Nat} → Heap A n zero
  node  : {l r n : Nat} → A → (p : Priority) → l ≥ r → p ≥ n → Heap A p l → Heap A p r → Heap A n (suc (l + r))

isEmpty : {A : Set} {n m : Nat} → Heap A n m → Bool
isEmpty empty            = true
isEmpty (node _ _ _ _ _ _) = false

-- here we use liberal singleton index
singleton : {A : Set} → A → Priority → Heap A zero (suc zero)
singleton x p = node x p ge0 ge0 empty empty


makeT : {A : Set} {l r n : Nat} → A → (p : Priority) → p ≥ n → Heap A p l → Heap A p r → Heap A n (suc (l + r))
makeT {A} {l-rank} {r-rank} {n} x p p≥n l r with order l-rank r-rank
makeT {A} {l-rank} {r-rank} {n} x p p≥n l r | ge lger
  = node x p lger p≥n l r
makeT {A} {l-rank} {r-rank} {n} x p p≥n l r | le rgel
  = subst (Heap A n) (cong suc (+comm r-rank l-rank)) (node x p rgel p≥n r l)

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

merge : {A : Set} {l r b : Nat} → Heap A b l → Heap A b r → Heap A b (l + r)
merge h1 h2 with h1 | h2
merge {A} {zero} {_} {_} h1 h2
          | empty
          | _
          = h2 -- See [merge, proof 0a]
merge {A} {suc l} {zero} {b} h1 h2
          | _
          | empty
          = subst (Heap A b)
                  (sym (+0 (suc l)))  -- See [merge, proof 0b]
                  h1
merge {A} {suc .(l1-rank + r1-rank)} {suc .(l2-rank + r2-rank)} {b}
          h1 h2
          | node {l1-rank} {r1-rank} x1 p1 l1≥r1 p1≥b l1 r1
          | node {l2-rank} {r2-rank} x2 p2 l2≥r2 p2≥b l2 r2
          with order p1 p2
merge {A} {suc .(l1-rank + r1-rank)} {suc .(l2-rank + r2-rank)} {b}
          h1 h2
          | node {l1-rank} {r1-rank} x1 p1 l1≥r1 p1≥b l1 r1
          | node {l2-rank} {r2-rank} x2 p2 l2≥r2 p2≥b l2 r2
          | le p1≤p2
          = subst (Heap A b)
                  (proof-1 l1-rank r1-rank l2-rank r2-rank) -- See [merge, proof 1]
                  (makeT x1 p1 p1≥b l1 (merge r1 (node x2 p2 l2≥r2 p1≤p2 l2 r2)))
merge {A} {suc .(l1-rank + r1-rank)} {suc .(l2-rank + r2-rank)} {b}
          h1 h2
          | node {l1-rank} {r1-rank} x1 p1 l1≥r1 p1≥b l1 r1
          | node {l2-rank} {r2-rank} x2 p2 l2≥r2 p2≥b l2 r2
          | ge p1≥p2
          = subst (Heap A b)
                  (proof-2 l1-rank r1-rank l2-rank r2-rank) -- See [merge, proof 2]
                  (makeT x2 p2 p2≥b l2 (merge r2 (node x1 p1 l1≥r1 p1≥p2 l1 r1)))

toZero : {A : Set} {n b : Nat} → Heap A b n → Heap A zero n
toZero empty                 = empty
toZero (node x p rank _ l r) = node x p rank ge0 l r

insert : {A : Set} {b n : Nat} → Priority → A → Heap A b n → Heap A zero (suc n)
insert p x h = merge (singleton x p) (toZero h)

findMin : {A : Set} {n b : Nat} → Heap A b (suc n) → A
findMin (node x _ _ _ _ _) = x

deleteMin : {A : Set} {n b : Nat} → Heap A b (suc n) → Heap A zero n
deleteMin (node _ _ _ _ l r) = merge (toZero l) (toZero r)
