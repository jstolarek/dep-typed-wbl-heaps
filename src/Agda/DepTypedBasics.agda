----------------------------------------------------------------------
-- Copyright: 2013, Jan Stolarek, Lodz University of Technology     --
--                                                                  --
-- License: See LICENSE file in root of the repo                    --
-- Repo address: https://github.com/jstolarek/dep-typed-heaps       --
--                                                                  --
-- This module reinvents the dependently typed wheel.  We need that --
-- wheel to get rollin.                                             --
----------------------------------------------------------------------

module DepTypedBasics where

open import Basics public hiding (_≥_ ; min)

data _≥_ : Nat → Nat → Set where
  ge0 : {y : Nat} → y ≥ zero
  geS : {x : Nat} {y : Nat} → x ≥ y → suc x ≥ suc y

data Order : Nat → Nat → Set where
  ge : {x : Nat} {y : Nat} → x ≥ y → Order x y
  le : {x : Nat} {y : Nat} → y ≥ x → Order x y

order : (a : Nat) → (b : Nat) → Order a b
order a       zero    = ge ge0
order zero    (suc b) = le ge0
order (suc a) (suc b) with order a b
order (suc a) (suc b) | ge ageb = ge (geS ageb)
order (suc a) (suc b) | le bgea = le (geS bgea)

min : {a b : Nat} → Order a b → Nat
min {a} {b} (ge _) = b
min {a} {b} (le _) = a

infixl 4 _≥_


data _≡_ {S : Set} (s : S) : S → Set where
  refl : s ≡ s

infixl 1 _≡_

sym : {A : Set} → {a b : A} → a ≡ b → b ≡ a
sym refl = refl

trans : {A : Set}{a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans refl refl = refl

cong : {A B : Set} (f : A → B) → ∀ {a b} → a ≡ b → f a ≡ f b
cong f refl = refl

subst : {A : Set}(P : A → Set) → {a b : A} → a ≡ b → P a → P b
subst prp refl p = p

subst2 : {A : Set}{P : A → Set} → {a b : A} → a ≡ b → P a → P b
subst2 refl p = p

+0 : (a : Nat) → a + zero ≡ a
+0 zero    = refl
+0 (suc a) = cong suc (+0 a)

+suc : (a b : Nat) → suc (a + b) ≡ a + (suc b)
+suc zero b    = refl
+suc (suc a) b = cong suc (+suc a b)

≥suc : {m n : Nat} → m ≡ n → m ≥ n
≥suc {zero} {zero} refl        = ge0
≥suc {.(suc n)} {(suc n)} refl = geS (≥suc {n} {n} refl)

+comm : (a b : Nat) → a + b ≡ b + a
+comm a zero    = +0 a
+comm a (suc b) = trans (sym (+suc a b)) (cong suc (+comm a b))

+assoc : (a b c : Nat) → a + (b + c) ≡ (a + b) + c
+assoc zero b c    = refl
+assoc (suc a) b c = cong suc (+assoc a b c) -- See [Associativity of addition]

-- Note [Associativity of addition]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
-- In the second case of +assoc I have to prove:
--
--   suc a + (b + c) ≡ (suc a + b) + c
--
-- Agda normalizes each side using definition of + :
--
--  LHS: suc a + (b + c) ≡ suc (a + (b + c))
--  RHS: (suc a + b) + c ≡ suc (a + b) + c ≡ suc ((a + b) + c)
--
-- This means I have to prove:
--
--   suc (a + (b + c)) ≡ suc ((a + b) + c)
--
-- I use cong to remove the outer suc on both sides which leaves me
-- with a proof of:
--
--   a + (b + c) ̄≡ (a + b) + c
--
-- Which happens to be my inductive hypothesis - hence a recursive
-- call to +assoc.

