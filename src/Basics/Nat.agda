----------------------------------------------------------------------
-- Copyright: 2013, Jan Stolarek, Lodz University of Technology     --
--                                                                  --
-- License: See LICENSE file in root of the repo                    --
-- Repo address: https://github.com/jstolarek/dep-typed-wbl-heaps   --
--                                                                  --
-- Definition of natural numbers and operations on them.            --
----------------------------------------------------------------------

module Basics.Nat where

open import Basics.Bool

-- Nat represents natural numbers (starting with 0)
data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

-- We define a constant 1 as it will be useful later on
one : Nat
one = suc zero

-- Addition
_+_ : Nat → Nat → Nat
zero  + m = m
suc n + m = suc (n + m)

infixl 6 _+_

-- Comparisons
-- _<_ : Nat → Nat → Bool
-- n     < zero  = false
-- zero  < suc n = true
-- suc n < suc m = n < m

-- _≥_ : Nat → Nat → Bool
-- m     ≥ zero  = true
-- zero  ≥ suc n = false
-- suc m ≥ suc n = m ≥ n

-- infixl 4 _<_ _≥_

-- min : Nat → Nat  → Nat
-- min zero    n       = zero
-- min (suc m) zero    = zero
-- min (suc m) (suc n) = suc (min m n)
