module Matrix.Split where

open import Data.Nat
open import Data.Fin using (Fin; fromℕ; fromℕ≤; toℕ;  raise; reduce≥) 
                     renaming (zero to f0; suc to fsuc)

open import Data.Integer using (ℤ; +_; _-_)
                        -- renaming (≥ to z≥)
open import Matrix.Definitions using (toℤ) renaming (_≥_ to _z≥_; _<_ to _z<_)
open import Data.Empty
open import Algebra
open import Algebra.Structures
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Function
open import Relation.Nullary.Core

open import Relation.Binary.HeterogeneousEquality using (_≅_; ≡-to-≅)
open Relation.Binary.HeterogeneousEquality.≅-Reasoning

open import Matrix.Abstract



data Splitting : Set where
  empty : Splitting -- no extent
  one : Splitting -- unsplittable
  deeper : Splitting -> Splitting -> Splitting -- what does pos do here?

splitSize : Splitting -> ℕ
splitSize = {!!}



data Splitted (a : Set) : Splitting -> Splitting → Set where
  one : (x : a) -> Splitted a one one
  empty : ∀ {r c} -> Splitted a r c -- either no extent, or zeros. => need ring
  quad : ∀ {r1 r2 c1 c2} -> (m11 : Splitted a r1 c1) -> (m12 : Splitted a r1 c2) -> 
                            (m21 : Splitted a r2 c1) -> (m22 : Splitted a r2 c2) 
          -> Splitted a (deeper r1 r2) (deeper c1 c2)



valiant : ∀ {a s} -> Splitted a s s -> Splitted a s s
valiant (one x) = {!!}
valiant empty = {!!}
valiant (quad x x₁ x₂ x₃) = {!!}