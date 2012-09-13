module Definitions where

open import Data.Nat          using (ℕ)
open import Data.Fin          using (Fin; toℕ)
open import Data.Integer      using (ℤ; suc; _≤_; +_)
open import Relation.Binary   using (Rel)
open import Relation.Nullary  using (¬_)
open import Level             using ()

-- Defining more inequalities for ℤ!
infix 4 _<_ _≥_ _>_ _≰_ _≮_ _≱_ _≯_

_<_ : Rel ℤ Level.zero
m < n = suc m ≤ n

_≥_ : Rel ℤ Level.zero
m ≥ n = n ≤ m

_>_ : Rel ℤ Level.zero
m > n = n < m

_≰_ : Rel ℤ Level.zero
a ≰ b = ¬ a ≤ b

_≮_ : Rel ℤ Level.zero
a ≮ b = ¬ a < b

_≱_ : Rel ℤ Level.zero
a ≱ b = ¬ a ≥ b

_≯_ : Rel ℤ Level.zero
a ≯ b = ¬ a > b

-- Helper function that takes a Fin to ℤ
toℤ : {n : ℕ} -> Fin n -> ℤ
toℤ x = + toℕ x
