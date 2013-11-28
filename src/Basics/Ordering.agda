----------------------------------------------------------------------
-- Copyright: 2013, Jan Stolarek, Lodz University of Technology     --
--                                                                  --
-- License: See LICENSE file in root of the repo                    --
-- Repo address: https://github.com/jstolarek/dep-typed-wbl-heaps   --
--                                                                  --
-- Definition of datatypes that represent ordering and functions    --
-- that operate on them. These datatypes are based on ideas         --
-- introduced in "Why Dependent Types Matter" (see bibliography).   --
----------------------------------------------------------------------

module Basics.Ordering where

open import Basics.Nat hiding (_≥_)

-- The ≥ type is a proof of greater-equal relation between two natural
-- numbers. It proofs that: a) any number is ≥ zero and b) any two
-- natural numbers are in ≥ relation if their predecessors are also in
-- that relation.
data _≥_ : Nat → Nat → Set where
  ge0 : {y : Nat}                   → y     ≥ zero
  geS : {x : Nat} {y : Nat} → x ≥ y → suc x ≥ suc y

infixl 4 _≥_

-- Order datatype tells whether two numbers are in ≥ relation or
-- not. In that sense it is an equivalent of Bool datatype. Unlike
-- Bool however, Order supplies a proof of WHY the numbers are (or are
-- not) in the ≥ relation.
data Order : Nat → Nat → Set where
  ge : {x : Nat} {y : Nat} → x ≥ y → Order x y
  le : {x : Nat} {y : Nat} → y ≥ x → Order x y

-- order function takes two natural numbers and compares them,
-- returning the result of comparison together with a proof of the
-- result.
order : (a : Nat) → (b : Nat) → Order a b
order a       zero    = ge ge0
order zero    (suc b) = le ge0
order (suc a) (suc b) with order a b
order (suc a) (suc b) | ge ageb = ge (geS ageb)
order (suc a) (suc b) | le bgea = le (geS bgea)

