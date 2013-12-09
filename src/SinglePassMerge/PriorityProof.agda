----------------------------------------------------------------------
-- Copyright: 2013, Jan Stolarek, Lodz University of Technology     --
--                                                                  --
-- License: See LICENSE file in root of the repo                    --
-- Repo address: https://github.com/jstolarek/dep-typed-wbl-heaps   --
--                                                                  --
-- Weight biased leftist heap that proves to maintain priority      --
-- invariant and uses a single-pass merging algorithm.              --
----------------------------------------------------------------------

{-# OPTIONS --sized-types #-}
module SinglePassMerge.PriorityProof where

open import Basics.Nat renaming (_≥_ to _≥ℕ_)
open import Basics
open import Sized

data Heap : {i : Size} → Priority → Set where
  empty : {i : Size} {n : Priority} → Heap {↑ i} n
  node  : {i : Size} {n : Priority} → (p : Priority) → Rank → p ≥ n →
          Heap {i} p → Heap {i} p → Heap {↑ i} n

rank : {b : Priority} → Heap b → Rank
rank empty            = zero
rank (node _ r _ _ _) = r

-- This implementation is derived in the same way as merge in
-- SinglePassMerge.NoProofs: depending on the size of new children we
-- swap parameters passed to node. Nothing really interesting.
merge : {i j : Size} {p : Nat} → Heap {i} p → Heap {j} p → Heap p
merge empty h2 = h2
merge h1 empty = h1
merge .{↑ i} .{↑ j}
  (node {i} p1 l-rank p1≥p l1 r1)
  (node {j} p2 r-rank p2≥p l2 r2)
  with order p1 p2
  | rank l1 ≥ℕ rank r1 + r-rank
  | rank l2 ≥ℕ rank r2 + l-rank
merge .{↑ i} .{↑ j}
  (node {i} p1 l-rank p1≥p l1 r1)
  (node {j} p2 r-rank p2≥p l2 r2)
  | le p1≤p2 | true | _
  = node p1 (l-rank + r-rank) p1≥p l1 (merge {i} {↑ j} r1 (node p2 r-rank p1≤p2 l2 r2))
merge .{↑ i} .{↑ j}
  (node {i} p1 l-rank p1≥p l1 r1)
  (node {j} p2 r-rank p2≥p l2 r2)
  | le p1≤p2 | false | _
  = node p1 (l-rank + r-rank) p1≥p (merge {i} {↑ j} r1 (node p2 r-rank p1≤p2 l2 r2)) l1
merge .{↑ i} .{↑ j}
  (node {i} p1 l-rank p1≥p l1 r1)
  (node {j} p2 r-rank p2≥p l2 r2)
  | ge p2≤p1 | _ | true
  = node p2 ((l-rank + r-rank)) p2≥p l2 (merge {↑ i} {j} (node p1 l-rank p2≤p1 l1 r1) r2)
merge .{↑ i} .{↑ j}
  (node {i} p1 l-rank p1≥p l1 r1)
  (node {j} p2 r-rank p2≥p l2 r2)
  | ge p2≤p1 | _ | false
  = node p2 ((l-rank + r-rank)) p2≥p (merge {↑ i} {j} (node p1 l-rank p2≤p1 l1 r1) r2) l2
