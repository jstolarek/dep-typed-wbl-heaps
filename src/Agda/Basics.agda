----------------------------------------------------------------------
-- Copyright: 2013, Jan Stolarek, Lodz University of Technology     --
--                                                                  --
-- License: See LICENSE file in root of the repo                    --
-- Repo address: https://github.com/jstolarek/dep-typed-heaps       --
--                                                                  --
-- This module reinvents the wheel.  We need that wheel to get      --
-- rollin.                                                          --
----------------------------------------------------------------------

module Basics where

-- BOOL AND CONDITIONALS
data Bool : Set where
  false : Bool
  true  : Bool

if_then_else_ : {A : Set} → Bool → A → A → A
if true  then x else _ = x
if false then _ else y = y

-- NATURAL NUMBERS
data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

one : Nat
one = suc zero

_<_ : Nat → Nat → Bool
n     < zero  = false
zero  < suc n = true
suc n < suc m = n < m

_≥_ : Nat → Nat → Bool
m     ≥ zero  = true
zero  ≥ suc n = false
suc m ≥ suc n = m ≥ n

infixl 4 _<_

min : Nat → Nat  → Nat
min zero    n       = zero
min (suc m) zero    = zero
min (suc m) (suc n) = suc (min m n)

_+_ : Nat → Nat → Nat
zero  + m = m
suc n + m = suc (n + m)
