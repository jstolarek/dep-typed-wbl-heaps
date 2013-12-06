----------------------------------------------------------------------
-- Copyright: 2013, Jan Stolarek, Lodz University of Technology     --
--                                                                  --
-- License: See LICENSE file in root of the repo                    --
-- Repo address: https://github.com/jstolarek/dep-typed-wbl-heaps   --
--                                                                  --
----------------------------------------------------------------------

{-# OPTIONS --sized-types #-}
module NoMakeT.CombinedProofs where

open import Basics
open import MakeT.RankProof   using    ( makeT-lemma )
                              renaming ( proof-1 to proof-1a; proof-2 to proof-2a )
open import NoMakeT.RankProof using    ( proof-1b; proof-2b )
open import Sized

data Heap : {i : Size} → Priority → Rank → Set where
  empty : {i : Size} {b : Priority} → Heap {↑ i} b zero
  node  : {i : Size} {b : Priority} → (p : Priority) → p ≥ b → {l r : Rank} → l ≥ r →
          Heap {i} p l → Heap {i} p r → Heap {↑ i} b (suc (l + r))

merge : {i j : Size} {b : Priority} {l r : Rank} → Heap {i} b l → Heap {j} b r
      → Heap {∞} b (l + r)
merge empty h2 = h2 -- See [merge, proof 0a]
merge {_} .{_} {b} {suc l} {zero} h1 empty
          = subst (Heap b)
                  (sym (+0 (suc l)))  -- See [merge, proof 0b]
                  h1
merge .{_} .{_} .{b} {suc .(l1-rank + r1-rank)} {suc .(l2-rank + r2-rank)}
  (node {_} .{b} p1 p1≥b {l1-rank} {r1-rank} l1≥r1 l1 r1)
  (node {_}  {b} p2 p2≥b {l2-rank} {r2-rank} l2≥r2 l2 r2)
  with order p1 p2
  | order l1-rank (r1-rank + suc (l2-rank + r2-rank))
  | order l2-rank (r2-rank + suc (l1-rank + r1-rank))
merge .{↑ i} .{↑ j}  .{b} {suc .(l1-rank + r1-rank)} {suc .(l2-rank + r2-rank)}
  (node {i}.{b} p1 p1≥b {l1-rank} {r1-rank} l1≥r1 l1 r1)
  (node {j} {b} p2 p2≥b {l2-rank} {r2-rank} l2≥r2 l2 r2)
  | le p1≤p2
  | ge l1≥r1+h2
  | _
  = subst (Heap b)
          (proof-1a l1-rank r1-rank l2-rank r2-rank) -- See [merge, proof 1a]
          (node p1 p1≥b l1≥r1+h2 l1 {!(merge r1 (node p2 p1≤p2 l2≥r2 l2 r2))!}) --(merge r1 (node p2 p1≤p2 l2≥r2 l2 r2)))
merge .{↑ i} .{↑ j} .{b} {suc .(l1-rank + r1-rank)} {suc .(l2-rank + r2-rank)}
  (node {i} .{b} p1 p1≥b {l1-rank} {r1-rank} l1≥r1 l1 r1)
  (node {j}  {b} p2 p2≥b {l2-rank} {r2-rank} l2≥r2 l2 r2)
  | le p1≤p2
  | le l1≤r1+h2
  | _
  = subst (Heap b)
          (proof-1b l1-rank r1-rank l2-rank r2-rank) -- See [merge, proof 1b]
          (node p1 p1≥b l1≤r1+h2 (merge r1 (node p2 p1≤p2 l2≥r2 l2 r2)) l1)
merge .{↑ i} .{↑ j}  .{b} {suc .(l1-rank + r1-rank)} {suc .(l2-rank + r2-rank)}
  (node {i} .{b} p1 p1≥b {l1-rank} {r1-rank} l1≥r1 l1 r1)
  (node {j}  {b} p2 p2≥b {l2-rank} {r2-rank} l2≥r2 l2 r2)
  | ge p1≥p2
  | _
  | ge l2≥r2+h1
  = subst (Heap b)
          (proof-2a l1-rank r1-rank l2-rank r2-rank) -- See [merge, proof 2a]
          (node p2 p2≥b l2≥r2+h1 l2 (merge r2 (node p1 p1≥p2 l1≥r1 l1 r1)))
merge .{↑ i} .{↑ j}  .{b} {suc .(l1-rank + r1-rank)} {suc .(l2-rank + r2-rank)}
  (node {i} .{b} p1 p1≥b {l1-rank} {r1-rank} l1≥r1 l1 r1)
  (node {j}  {b} p2 p2≥b {l2-rank} {r2-rank} l2≥r2 l2 r2)
  | ge p1≥p2
  | _
  | le l2≤r2+h1
  = subst (Heap b)
          (proof-2b l1-rank r1-rank l2-rank r2-rank) -- See [merge, proof 2b]
          (node p2 p2≥b l2≤r2+h1 (merge r2 (node p1 p1≥p2 l1≥r1 l1 r1)) l2)
