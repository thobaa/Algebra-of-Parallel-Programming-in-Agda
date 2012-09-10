module Definitions where

-- Either datatype (don't know if there is another buillt in for "or")
--   PJ: There is Data.Sum 
data Either (A : Set) (B : Set) : Set where
  left   : (x : A) -> Either A B
  right  : (y : B) -> Either A B

-- Inspired by Haskell! (Or "or-elimination")
fromEither : {A B C : Set} -> (A -> C) -> (B -> C) -> Either A B -> C
fromEither f _ (left x) = f x 
fromEither _ g (right y) = g y


open import Data.Nat          using (ℕ)
open import Data.Fin          hiding (_<_; suc; _≤_)
open import Data.Integer      using (ℤ; suc; _≤_; +_)
open import Relation.Binary   using (Rel)
open import Relation.Nullary  using (¬_)
open import Level             hiding (suc)

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
