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

-- Rank of a weight biased leftist heap is defined as number of nodes
-- in a heap. In other words it is size of a tree used to represent a
-- heap.
Rank : Set
Rank = Nat

-- Priority assigned to elements stored in a Heap.
--
-- CONVENTION: Lower number means higher Priority. Therefore the
-- highest Priority is zero. It will sometimes be more convenient not
-- to use this inversed terminology. We will then use terms "smaller"
-- and "greater" (in contrast to "lower" and "higher"). Example:
-- Priority 3 is higher than 5, but 3 is smaller than 5.
Priority : Set
Priority = Nat

-- Note that both Rank and Priority are Nat, which allows us to
-- operate on them with functions that work for Nat.
