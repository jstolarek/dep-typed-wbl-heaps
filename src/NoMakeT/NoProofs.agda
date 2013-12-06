----------------------------------------------------------------------
-- Copyright: 2013, Jan Stolarek, Lodz University of Technology     --
--                                                                  --
-- License: See LICENSE file in root of the repo                    --
-- Repo address: https://github.com/jstolarek/dep-typed-wbl-heaps   --
--                                                                  --
----------------------------------------------------------------------

{-# OPTIONS --sized-types #-}
module NoMakeT.NoProofs where

open import Basics.Nat
open import Basics hiding (_≥_)
open import Sized

data Heap : {i : Size} → Set where
  empty : {i : Size} → Heap {↑ i}
  node  : {i : Size} → Priority → Rank → Heap {i} → Heap {i} → Heap {↑ i}

rank : Heap → Nat
rank empty          = zero
rank (node _ r _ _) = r

merge : {i j : Size} → Heap {i} → Heap {j} → Heap
merge empty h2 = h2
merge h1 empty = h1
merge (node p1 w1 l1 r1) (node p2 w2 l2 r2) with p1 < p2
  | rank l1 ≥ rank r1 + w2
  | rank l2 ≥ rank r2 + w1
merge (node p1 w1 l1 r1) (node p2 w2 l2 r2)
  | true | true | _   = node p1 (w1 + w2) l1 (merge r1 (node p2 w2 l2 r2))
merge (node p1 w1 l1 r1) (node p2 w2 l2 r2)
  | true | false | _  = node p1 (w1 + w2) (merge r1 (node p2 w2 l2 r2)) l1
merge (node p1 w1 l1 r1) (node p2 w2 l2 r2)
  | false | _ | true  = node p2 (w1 + w2) l2 (merge r2 (node p1 w1 l1 r1))
merge (node p1 w1 l1 r1) (node p2 w2 l2 r2)
  | false | _ | false = node p2 (w1 + w2) (merge r2 (node p1 w1 l1 r1)) l2
