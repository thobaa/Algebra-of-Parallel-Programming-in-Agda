-- Standard library:
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Integer using (+_; _-_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Product using (Σ)

-- Own:
open import Valiant.Abstract.NonAssociativeNonRing using (NonAssociativeNonRing)
open import Valiant.MatrixAlgebra.Definitions using (toℤ; _<_)

import Valiant.Helper.Definitions using (R0)
import Valiant.Abstract.Matrix using (Matrix)


module Valiant.Abstract.Triangle {l₁ l₂} (NAR : NonAssociativeNonRing l₁ l₂) where

-- Parametrised
open Valiant.Helper.Definitions NAR
open Valiant.Abstract.Matrix NAR

IsTriangular : ∀ {m n} -> (d : ℕ) -> (A : Matrix m n) -> Set l₁
IsTriangular {m} {n} d A = (i : Fin m) → (j : Fin n) → 
                           (toℤ j - toℤ i < + d) → A i j ≡ R0


Triangle : ℕ -> Set l₁
Triangle n = Σ (Matrix n n) (λ A → IsTriangular 1 A)