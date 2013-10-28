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

data Bool : Set where
  false : Bool
  true  : Bool

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
n     ≥ zero  = true
zero  ≥ suc m = false
suc n ≥ suc m = n ≥ m

min : Nat → Nat → Nat
min n m with n ≥ m
min n m | true  = m
min n m | false = n

infixl 4 _<_ _≥_

_+_ : Nat → Nat → Nat
zero  + m = m
suc n + m = suc (n + m)

if_then_else_ : {A : Set} → Bool → A → A → A
if true  then x else _ = x
if false then _ else y = y

-- CODE BELOW IS NOT MINE

-- taken from Conor McBride's "Dependently typed metaprogramming (in Agda)
-- https://github.com/pigworker/MetaprogAgda/blob/master/Basics.agda

postulate
      Level : Set
      lzero : Level
      lsuc  : Level -> Level
      lmax  : Level -> Level -> Level

{-# BUILTIN LEVEL Level #-}
{-# BUILTIN LEVELZERO lzero #-}
{-# BUILTIN LEVELSUC lsuc #-}
{-# BUILTIN LEVELMAX lmax #-}

data _==_ {l}{X : Set l}(x : X) : X -> Set l where
  refl : x == x
infix 1 _==_

{-# BUILTIN EQUALITY _==_ #-}
{-# BUILTIN REFL refl #-}

-- taken from Relation/Binary/PropositionalEquality
cong : ∀ {a b} {A : Set a} {B : Set b}
       (f : A → B) {x y} → x == y → f x == f y
cong f refl = refl

-- taken from http://stackoverflow.com/questions/12949323/agda-type-checking-and-commutativity-associativity-of
rightIdentity : (n : Nat) -> (n + zero) == n
rightIdentity zero = refl
rightIdentity (suc n) = cong suc (rightIdentity n)
