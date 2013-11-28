----------------------------------------------------------------------
-- Copyright: 2013, Jan Stolarek, Lodz University of Technology     --
--                                                                  --
-- License: See LICENSE file in root of the repo                    --
-- Repo address: https://github.com/jstolarek/dep-typed-heaps       --
--                                                                  --
-- Defines heap abstraction                                         --
----------------------------------------------------------------------

module Heap where

open import Basics

-- Note that unlike in Haskell implementation, Priority is now a
-- natural number, not an integer.
Priority : Set
Priority = Nat

record Heap (H : Set → Set) : Set1 where
  field
    empty   : ∀ {A} → H A
    isEmpty : ∀ {A} → H A → Bool

    singleton : ∀ {A} → Priority → A → H A

    merge  : ∀ {A} → H A → H A → H A
    insert : ∀ {A} → Priority → A → H A → H A

    findMin   : ∀ {A} → H A → A
    deleteMin : ∀ {A} → H A → H A
open Heap {{...}} public
