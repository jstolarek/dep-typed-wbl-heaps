module DepTypedWeightedHeapMakeTHeapProperty

Priority : Type
Priority = Nat

Rank : Type
Rank = Nat

data (>=) : Nat -> Nat -> Type where
  ge0 : {y : Nat} -> y >= Z
  geS : {x : Nat} -> {y : Nat} -> (x >= y) -> (S x >= S y)

data Order : Nat -> Nat -> Type where
  ge : {x : Nat} -> {y : Nat} -> x >= y -> Order x y
  le : {x : Nat} -> {y : Nat} -> y >= x -> Order x y

order : (a : Nat) -> (b : Nat) -> Order a b
order _     Z      = ge ge0
order Z     (S b)  = le ge0
order (S a) (S b) with (order a b)
  | ge ageb = ge (geS ageb)
  | le bgea = le (geS bgea)


using (A : Type)
  data Heap : A -> Nat -> Type where
    empty : {n : Nat} -> Heap A n
    node  : {n : Nat} -> A -> (p : Priority) -> Rank -> p >= n  -> Heap A p -> Heap A p -> Heap A n

rank : {A : Type} -> {n : Nat} -> Heap A n -> Nat
rank empty              = Z
rank (node _ _ r _ _ _) = r

isEmpty : {A : Type} ->  {n : Nat} -> Heap A n -> Bool
isEmpty empty              = True
isEmpty (node _ _ _ _ _ _) = False

singletonL : {A : Type} -> A -> (p : Priority) -> Heap A Z
singletonL x p = node x p 1 ge0 empty empty

{-
singletonC : {A : Type} -> A -> (p : Priority) -> Heap A p
singletonC x p = node x p 1 (≥sym refl) empty empty

makeT : {A : Type} {n : Nat} -> A -> (p : Priority) -> p ≥ n -> Heap A p -> Heap A p -> Heap A n
makeT x p pgen l r with rank l | rank r
makeT x p pgen l r | l-rank | r-rank with order l-rank r-rank
makeT x p pgen l r | l-rank | r-rank | ge _ = node x p (suc (l-rank + r-rank)) pgen l r
makeT x p pgen l r | l-rank | r-rank | le _ = node x p (suc (l-rank + r-rank)) pgen r l

merge : {A : Type} {b : Nat} -> Heap A b -> Heap A b -> Heap A b
merge h1 h2 with h1 | h2
merge {A} {b} h1 h2
          | empty
          | _
          = h2
merge {A} {b} h1 h2
          | _
          | empty
          = h1
merge {A} {b} h1 h2
          | node x1 p1 l-rank p1≥b l1 r1
          | node x2 p2 r-rank p2≥b l2 r2
          with order p1 p2
merge {A} {b} h1 h2
          | node x1 p1 l-rank p1≥b l1 r1
          | node x2 p2 r-rank p2≥b l2 r2
          | le p1≤p2
          = makeT x1 p1 p1≥b l1 (merge r1 (node x2 p2 r-rank p1≤p2 l2 r2))
merge {A} {b} h1 h2
          | node x1 p1 l-rank p1≥b l1 r1
          | node x2 p2 r-rank p2≥b l2 r2
          | ge p1≥p2
          = makeT x2 p2 p2≥b l2 (merge r2 (node x1 p1 l-rank p1≥p2 l1 r1))

-- Again, termination checker problems. I can't create a function that
-- just replaces the proof, because Heap's index doesn't say anything
-- about index of its children and the new proof refers to index of
-- children.

toZero : {A : Type} {n : Nat} -> Heap A n -> Heap A zero
toZero empty                 = empty
toZero (node x p rank _ l r) = node x p rank ge0 l r

insertL : {A : Type} {n : Nat} -> A -> Priority -> Heap A n -> Heap A zero
insertL x p h = merge (singletonL x p) (toZero h)

-- This feels too conservative
insertC : {A : Type} -> A -> (p : Priority) -> Heap A p -> Heap A p
insertC x p h = merge (singletonC x p) h

-- We could write this function, but it would be very inconvenient to
-- require a proof each time we want to insert something.
insert : {A : Type} {n : Nat} -> A -> (p : Priority) -> n ≥ p -> Heap A n -> Heap A p
insert x p n≥p h = merge {!!} {!!}

-- Again, findMin and deletMin are incomplete
findMin : {A : Type} {n : Nat} -> Heap A n -> A
findMin empty              = {!!}
findMin (node x _ _ _ _ _) = x

deleteMin : {A : Type} {n b : Nat} -> Heap A n -> Heap A zero
deleteMin empty                               = {!!}
deleteMin {A} {n} {b} (node x p rank p≥n l r) = merge (toZero l) (toZero r)

-}