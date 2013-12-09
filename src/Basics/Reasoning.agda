----------------------------------------------------------------------
-- Copyright: 2013, Jan Stolarek, Lodz University of Technology     --
--                                                                  --
-- License: See LICENSE file in root of the repo                    --
-- Repo address: https://github.com/jstolarek/dep-typed-wbl-heaps   --
--                                                                  --
-- Refl datatype and functions required for equational reasoning.   --
----------------------------------------------------------------------

module Basics.Reasoning where

open import Basics.Nat hiding (_≥_)
open import Basics.Ordering

-- Basic definition we will need in our proofs is propositional
-- equality (known as refl). Unlike refl definition provided by Agda's
-- standard library the definition below is not universe
-- polymorphic. It works only on Set, but not on Set1 and higher Sets
-- - this will be perfectly sufficient for our purposes. This datatype
-- allows to express equality between types belonging to Set.
data _≡_ {S : Set} (s : S) : S → Set where
  refl : s ≡ s

infixl 1 _≡_

-- Below we prove basic properties of relations: symmetry,
-- transitivity, congruence and substitution. If these proofs are not
-- familiar I encourage to take a look at one of tutorials mentioned
-- in Section 1.3 ("Assumptions and conventions") of the paper.
sym : {A : Set} → {a b : A} → a ≡ b → b ≡ a
sym refl = refl

trans : {A : Set}{a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans refl refl = refl

cong : {A B : Set} (f : A → B) → ∀ {a b} → a ≡ b → f a ≡ f b
cong f refl = refl

subst : {A : Set}(P : A → Set) → {a b : A} → a ≡ b → P a → P b
subst prp refl p = p

-- We prove some basic properties of addition that we will need later
-- in more complex proofs. I assume that you had previous exposure to
-- these basic proofs, but nevertheless I provide extensive
-- explanations. Make sure you understand how these proofs work before
-- proceeding with rest of the paper.

-- Note [0 is right identity of addition]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
-- The fact that 0 is left identity of addition (ie. 0 + a ≡ a)
-- follows directly from our definition of _+_:
--
--   _+_ : Nat → Nat → Nat
--   zero  + m = m
--   suc n + m = suc (n + m)
--
-- But we need a separate proof that 0 is also right identity of
-- addition, ie. a + 0 ≡ a. Proof proceeds by induction on a. If a is
-- zero then we have:
--
--   0 + 0 = 0
--
-- And the proof follows from the definition of addition - hence we
-- use refl. In a recursive case we have:
--
--   (suc a) + zero ≡ (suc a)
--
-- Applying definition of addition to LHS we have:
--
--   suc (a + zero) ≡ suc a
--
-- Since we have suc on both sides of the equality, we use
-- congruence. This leaves us with a proof that equality holds for the
-- parameters of suc:
--
--   a + zero ≡ a
--
-- But that happens to be the equality we are proving at the
-- moment. We therefore make a recursive call to (+0 a), which is
-- equivalent of applying inductive hypothesis in an inductive proof.
--
-- ∎

+0 : (a : Nat) → a + zero ≡ a -- See Note [0 is right identity of addition]
+0 zero    = refl
+0 (suc a) = cong suc (+0 a)

-- Note [1 + (a + b) equals a + (1 + b)]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
-- We will need this property surprisingly often. We proceed by
-- inductive proof on a. In the base case, when a = 0, we have:
--
--   suc (0 + b) ≡ 0 + (suc b)
--
-- Applying definition of + to both sides of equality we get:
--
--   suc b ≡ suc b
--
-- Which is true by definition, hence we use refl. In the recursive
-- case we have:
--
--   suc ((suc a) + b) ≡ (suc a) + (suc b)
--
-- We apply definition of + to both sides and get:
--
--   suc (suc (a + b)) ≡ suc (a + (suc b))
--
-- Again, since we have suc on both sides we use congruence and are
-- left with a proof:
--
--   suc (a + b) ≡ a + (suc b)
--
-- Which again is the equality we are proving. We appeal to inductive
-- hypothesis by making a recursive call.
--
-- ∎

+suc : (a b : Nat) → suc (a + b) ≡ a + (suc b)
+suc zero b    = refl
+suc (suc a) b = cong suc (+suc a b)

-- Note [Commutativity of addition]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
-- Everyone knows that a + b ≡ b + a. But Agda won't take our word and
-- requires a formal proof. Let's proceed by induction on second
-- argument. In the base case we have:
--
--   a + 0 ≡ 0 + a
--
-- Right side reduces by the definition of + which leaves us with
--
--   a + 0 ≡ a
--
-- We proved that earlier so we appeal to already existing proof. In
-- the inductive case we have:
--
--   a + suc b ≡ (suc b) + a      [1]
--
-- Right hand side reduces by definition of + giving us:
--
--   a + suc b ≡ suc (b + a)      [2]
--
-- [2] is therefore the equality we have to prove. From +suc we know
-- that
--
--   suc (a + b) ≡ a + (suc b)    [3]
--
-- And we can use that to transform left hand side of [1]. Note
-- however that in order to apply [3] to left hand side of [1] we need
-- to reverse sides of the equality [3]:
--
--   a + (suc b) ≡ suc (a + b)    [4]
--
-- We achieve this by using symmetry.
--
-- Looking at right hand sides of [2] and [4] we see they differ by
-- the order of arguments to +. We can prove them equal by using
-- congruence on suc and appealing to our inductive hypothesis of
-- commutativity of addition. This means we have proven two things:
--
--   a + (suc b) ≡ suc (a + b)   [4, repeated], from symmetry of +suc
--   suc (a + b) ≡ suc (b + a)   [5], from congruence on suc and
--                               inductive hypothesis
--
-- Combining [4] and [5] using transitivity yields the proof of [2].
--
-- ∎
--
-- Here is a diagram, showing how code relates to the proof:
--
--                                 a + b ≡ b + a
--                                   ____|____
--                                  /         \
-- trans (sym (+suc a b)) (cong suc (+comm a b))
--       ̲\_____________/   \__________________/
--              |                    |
--  a + (suc b) ≡ suc (a + b)        |
--                       suc (a + b) ≡ suc (b + a)

+comm : (a b : Nat) → a + b ≡ b + a
+comm a zero    = +0 a
+comm a (suc b) = trans (sym (+suc a b)) (cong suc (+comm a b))

-- Note [Associativity of addition]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
-- We proceed by induction on the first parameter. In the base case we
-- have a = 0:
--
--   0 + (b + c) ≡ (0 + b) + c
--
-- Both sides can be normalized using the definition of + giving us
--
--   b + c ≡ b + c
--
-- Since this is true by definition we use refl. In the inductive case
-- we have to prove:
--
--   suc a + (b + c) ≡ (suc a + b) + c
--
-- Again, Agda normalizes each side using definition of + :
--
--   LHS: suc a + (b + c) ≡ suc (a + (b + c))
--   RHS: (suc a + b) + c ≡ suc (a + b) + c ≡ suc ((a + b) + c)
--
-- This means we have to prove:
--
--   suc (a + (b + c)) ≡ suc ((a + b) + c)
--
-- We can use congruence to remove the outer suc on both sides which
-- leaves us with a proof of:
--
--   a + (b + c) ̄≡ (a + b) + c
--
-- Which happens to be our inductive hypothesis - hence a recursive
-- call to +assoc.
--
-- ∎

+assoc : (a b c : Nat) → a + (b + c) ≡ (a + b) + c
+assoc zero b c    = refl
+assoc (suc a) b c = cong suc (+assoc a b c)

-- Note [If numbers are equal they are in the greater-equal relation]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
-- Finally, we need a proof that if a = b then a ≥ b. This property is
-- specific to our task, so you most likely haven't seen it other
-- tutorials. There are three interesting things in this proof:
--
--  1) a value of type m ≥ n proves that m is greater-equal than n. We
--     therefore need to construct the value of this type.
--
--  2) since refl is the only constructor of type ≡ we always use refl
--     when pattern matching on a value of ≡. We also always pass refl
--     as a value of ≡ in calls.
--
--  3) we need to match on implicit parameters to construct a
--     proof. Note that although type signature specifies Nats m and
--     n, in the proof we require that these are always equal.  This
--     requirement comes from the fact that m ≡ n, i.e. that m and n
--     are equal.
--
-- In the base case we need to construct a proof that 0 ≥ 0, which we
-- do by using ge0. Inductive case simply applies geS to result of
-- recursive call to ≥sym.

≥sym : {m n : Nat} → m ≡ n → m ≥ n
≥sym {zero}     {zero}    refl = ge0
≥sym {.(suc n)} {(suc n)} refl = geS (≥sym {n} {n} refl)
