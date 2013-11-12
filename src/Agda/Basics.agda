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

data _≥_ : Nat → Nat → Set where
  ge0 : {y : Nat} → y ≥ zero
  geS : {x : Nat} {y : Nat} → x ≥ y → suc x ≥ suc y

data Order : Nat → Nat → Set where
  ge : {x : Nat} {y : Nat} → x ≥ y → Order x y
  le : {x : Nat} {y : Nat} → y ≥ x → Order x y

order : (x : Nat) → (y : Nat) → Order x y
order x       zero    = ge ge0
order zero    (suc y) = le ge0
order (suc x) (suc y) with order x y
order (suc x) (suc y) | ge xgey = ge (geS xgey)
order (suc x) (suc y) | le ygex = le (geS ygex)

min : {m n : Nat} → Order m n → Nat
min {m} {n} (ge _) = n
min {m} {n} (le _) = m

infixl 4 _<_ _≥_

_+_ : Nat → Nat → Nat
zero  + m = m
suc n + m = suc (n + m)

data _≡_ {S : Set} (s : S) : S → Set where
  refl : s ≡ s

infixl 1 _≡_

sym : {A : Set} → {a b : A} → a ≡ b → b ≡ a
sym refl = refl

cong : {A B : Set} (f : A → B) → ∀ {x y} → x ≡ y → f x ≡ f y
cong f refl = refl

subst : {A : Set}(P : A → Set) → {a b : A} → a ≡ b → P a → P b
subst prp refl p = p

+0 : (n : Nat) → n + zero ≡ n
+0 zero    = refl
+0 (suc n) = cong suc (+0 n)

+suc : (m n : Nat) → suc (m + n) ≡ m + (suc n)
+suc zero n = refl
+suc (suc m) n = cong suc (+suc m n)

≥suc : {m n : Nat} → m ≡ n → m ≥ n
≥suc {zero} {zero} refl        = ge0
≥suc {.(suc n)} {(suc n)} refl = geS (≥suc {n} {n} refl)
