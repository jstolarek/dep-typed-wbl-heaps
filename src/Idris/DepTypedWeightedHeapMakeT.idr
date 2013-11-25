module DepTypedWeightedHeapMakeT

data (>=) : Nat -> Nat -> Type where
  ge0 : {y : Nat} -> y >= Z
  geS : {x : Nat} -> {y : Nat} -> x >= y -> (S x) >= (S y)


Priority : Type
Priority = Nat

using (A : Type)
  data Heap : A -> Nat -> Type where
    empty : Heap A Z
    node  : {l : Nat} -> {r : Nat} -> (l >= r) -> Priority -> A -> Heap A l -> Heap A r -> Heap A (S (l + r))

-- not an interestng function
isEmpty : {A : Type} -> {n : Nat} -> Heap A n -> Bool
isEmpty empty            = True
isEmpty (node _ _ _ _ _) = False

singleton : {A : Type} -> Priority -> A -> Heap A (S Z)
singleton p x = node ge0 p x empty empty


{-

makeT : {A : Type} {l r : Nat} -> Priority -> A -> Heap A l -> Heap A r -> Heap A (S (l + r))
makeT {A} {l-rank} {r-rank} p x l r with order l-rank r-rank
  | ge lger = node lger p x l r
makeT {A} {l-rank} {r-rank} p x l r | le rgel
  = subst (Heap A) (cong S (+comm r-rank l-rank)) (node rgel p x r l)

proof-1 : (l1 r1 l2 r2 : Nat) -> S ( l1 + (r1 + S (l2 + r2)))
                              ≡ S ((l1 + r1) + S (l2 + r2))
proof-1 l1 r1 l2 r2 = cong S (+assoc l1 r1 (S (l2 + r2)))



lemma-A : (n m : Nat) -> n + S m ≡ m + S n
lemma-A n m = trans (sym (+S n m)) (trans (cong S (+comm n m)) (+S m n))

lemma-B : (a b c : Nat) -> a + (b + S c) ≡ c + S (a + b)
lemma-B a b c = trans (+assoc a b (S c)) (lemma-A (a + b) c)

proof-2 : (l1 r1 l2 r2 : Nat) -> S (l2 + (r2  + S (l1 + r1)))
                              ≡ S ((l1 + r1) + S (l2 + r2))
proof-2 l1 r1 l2 r2 = cong S (lemma-B l2 r2 (l1 + r1))


merge : {A : Type} {l r : Nat} -> Heap A l -> Heap A r -> Heap A (l + r)
merge h1 h2 with h1 | h2
merge {A} {Z} {_} h1 h2
          | empty
          | _
          = h2 -- See [merge, proof 0a]
merge {A} {S l} {Z} h1 h2
          | _
          | empty
          = subst (Heap A)
                  (sym (+0 (S l)))  -- See [merge, proof 0b]
                  h1
merge {A} {S .(l1-rank + r1-rank)} {S .(l2-rank + r2-rank)}
          h1 h2
          | node {l1-rank} {r1-rank} l1ger1 p1 x1 l1 r1
          | node {l2-rank} {r2-rank} l2ger2 p2 x2 l2 r2
          with p1 < p2
merge {A} {S .(l1-rank + r1-rank)} {S .(l2-rank + r2-rank)}
          h1 h2
          | node {l1-rank} {r1-rank} l1ger1 p1 x1 l1 r1
          | node {l2-rank} {r2-rank} l2ger2 p2 x2 l2 r2
          | true
          = subst (Heap A)
                  (proof-1 l1-rank r1-rank l2-rank r2-rank) -- See [merge, proof 1]
                  (makeT p1 x1 l1 (merge r1 h2))
merge {A} {S .(l1-rank + r1-rank)} {S .(l2-rank + r2-rank)}
          h1 h2
          | node {l1-rank} {r1-rank} l1ger1 p1 x1 l1 r1
          | node {l2-rank} {r2-rank} l2ger2 p2 x2 l2 r2
          | false
          = subst (Heap A)
                  (proof-2 l1-rank r1-rank l2-rank r2-rank) -- See [merge, proof 2]
                  (makeT p2 x2 l2 (merge r2 h1))

insert : {A : Type} {n : Nat} -> Priority -> A -> Heap A n -> Heap A (S n)
insert p x h = merge (singleton p x) h

findMin : {A : Type} {n : Nat} -> Heap A (S n) -> A
findMin (node _ _ x _ _) = x

deleteMin : {A : Type} {n : Nat} -> Heap A (S n) -> Heap A n
deleteMin (node _ _ _ l r) = merge l r

-}