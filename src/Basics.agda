----------------------------------------------------------------------
-- Copyright: 2013, Jan Stolarek, Lodz University of Technology     --
--                                                                  --
-- License: See LICENSE file in root of the repo                    --
-- Repo address: https://github.com/jstolarek/dep-typed-wbl-heaps   --
--                                                                  --
-- This module re-exports all Basics/* modules for convenience.     --
-- Note that both Basics.Nat and Basics.Ordering define ≥ operator. --
-- Here we re-export the one from Basics.Ordering as it will be     --
-- used most of the time.                                           --
-- This module also defines two type synonyms that will be helpful  --
-- when working on heaps: Rank and Priority.                        --
----------------------------------------------------------------------

module Basics where

open import Basics.Bool      public
open import Basics.Nat       public hiding (_≥_)
open import Basics.Ordering  public
open import Basics.Reasoning public

-- Rank of a weight biased leftist heap defined as number of nodes in
-- a heap.
Rank : Set
Rank = Nat

-- Priority assigned to elements stored in a Heap. 0 represents the
-- highest priority.
Priority : Set
Priority = Nat

-- Note that both Rank and Priority are Nat, which allows us to
-- operate on them with functions that work for Nat.
