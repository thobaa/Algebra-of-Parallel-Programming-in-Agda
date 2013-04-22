-- Standard library:
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; _≤_)
open import Data.Integer using (+_; _-_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Product using (Σ)
open import Level using (_⊔_)


-- Own:
open import Valiant.Abstract.NonAssociativeNonRing
open import Valiant.MatrixAlgebra.Definitions using (toℤ; _<_)

--import Valiant.Helper.Definitions using (R0)
import Valiant.Abstract.Matrix using (Matrix)


module Valiant.Abstract.Triangle {l₁ l₂} (NAR : NonAssociativeNonRing l₁ l₂) where

-- Parametrised
--open Valiant.Helper.Definitions NAR
open Valiant.Abstract.Matrix NAR
open NonAssociativeNonRing NAR renaming (_≈_ to _R≈_; 0# to R0)

-- we use a simpler version, the only problem might be for the sum-spec translation.
--IsTriangular : ∀ {m n} -> (d : ℕ) -> (A : Matrix m n) -> Set l₁
--IsTriangular {m} {n} d A = (i : Fin m) → (j : Fin n) → 
--                           (toℤ j - toℤ i < + d) → A i j ≡ R0
IsTriangular : ∀ {n} → (A : Matrix n n) → Set l₂
IsTriangular {n} A = (i j : Fin n) → j ≤ i → A i j R≈ R0 

record Triangle (n : ℕ) : Set (l₁ ⊔ l₂) where
  field 
    matrix : Matrix n n
    proof  : IsTriangular matrix

--Triangle : ℕ -> Set l₁
--Triangle n = Σ (Matrix n n) (λ A → IsTriangular 1 A)