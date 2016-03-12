-- Standard library:
open import Data.Nat using (ℕ; _+_; zero; suc; _≤?_; ≤-pred; s≤s; z≤n; _∸_; pred) renaming (_≤_ to _ℕ≤_)
open import Data.Nat.Properties using (≰⇒>)
open import Data.Fin using (Fin; _≤_; toℕ; reduce≥; fromℕ≤) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (toℕ-fromℕ≤)
open import Data.Integer using (+_; _-_)
open import Data.Empty using (⊥-elim)
open import Relation.Binary using (_Preserves₂_⟶_⟶_)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_) renaming (sym to ≡-sym; refl to ≡-refl; cong to ≡-cong)
import Relation.Binary.EqReasoning as EqR
open import Data.Product using (Σ)
open import Level using (_⊔_)
open import Relation.Nullary

-- Own:
open import Valiant.Abstract.NonAssociativeNonRing
open import Valiant.MatrixAlgebra.Definitions using (toℤ; _<_)

import Valiant.Abstract.Matrix 


module Valiant.Abstract.Triangle {l₁ l₂} (NAR : NonAssociativeNonRing l₁ l₂) where

-- Parametrised

import Valiant.Helper.Definitions
open Valiant.Helper.Definitions NAR using (reduce≤)
--open Valiant.Helper.Definitions NAR
open Valiant.Abstract.Matrix NAR
open NonAssociativeNonRing NAR renaming (_≈_ to _R≈_; _+_ to _R+_; zero to Rzero)

-- we use a simpler version, the only problem might be for the sum-spec translation.
--IsTriangular : ∀ {m n} -> (d : ℕ) -> (A : Matrix m n) -> Set l₁
--IsTriangular {m} {n} d A = (i : Fin m) → (j : Fin n) → 
--                           (toℤ j - toℤ i < + d) → A i j ≡ R0
IsTriangular : ∀ {n} → (A : Matrix n n) → Set l₂
IsTriangular {n} A = (i j : Fin n) → j ≤ i → A i j R≈ 0# 

record Triangle (n : ℕ) : Set (l₁ ⊔ l₂) where
  field 
    matrix : Matrix n n
    proof  : IsTriangular matrix

zeroTriangle : {n : ℕ} → Triangle n
zeroTriangle = record { matrix = zeroMatrix; proof = λ i j x → refl }

--Triangle : ℕ -> Set l₁
--Triangle n = Σ (Matrix n n) (λ A → IsTriangular 1 A)

-- not here!!!
from≡ : {x y : Carrier} → x ≡ y → x R≈ y
from≡ PropEq.refl = refl
i≤j⇒i∸k≤j∸k : {i j : ℕ} (k : ℕ) → i ℕ≤ j → i ∸ k ℕ≤ j ∸ k
i≤j⇒i∸k≤j∸k zero i≤j = i≤j
i≤j⇒i∸k≤j∸k (suc n) z≤n = z≤n
i≤j⇒i∸k≤j∸k (suc n) (s≤s m≤n) = i≤j⇒i∸k≤j∸k n m≤n

i∸m≡reduce≥-i-m≤i : {m n : ℕ} → (i : Fin (m + n)) → (p : m ℕ≤ toℕ i) → toℕ i ∸ m ≡ toℕ (reduce≥ i p)
i∸m≡reduce≥-i-m≤i {zero} i z≤n = ≡-refl
i∸m≡reduce≥-i-m≤i {suc m} fzero ()
i∸m≡reduce≥-i-m≤i {suc m} (fsuc i) (s≤s m≤n) = i∸m≡reduce≥-i-m≤i i m≤n

Three-proof : {m n : ℕ} → (U : Triangle m) (R : Matrix m n) (L : Triangle n) → 
            IsTriangular (Four (Triangle.matrix U) R
                               zeroMatrix          (Triangle.matrix L))
Three-proof {m} {n} U R L i j j≤i with suc (toℕ i) ≤? m | suc (toℕ j) ≤? m
Three-proof {m} {n} U R L i j j≤i | yes p | yes p' = Triangle.proof U (fromℕ≤ p) (fromℕ≤ p') (begin 
  toℕ (fromℕ≤ p') 
    ≡⟨ toℕ-fromℕ≤ p' ⟩ 
  toℕ j
    ≤⟨ j≤i ⟩
  toℕ i
    ≡⟨ ≡-sym (toℕ-fromℕ≤ p) ⟩ 
  toℕ (fromℕ≤ p) ∎)
  where open Data.Nat.≤-Reasoning
Three-proof {m} U R L i j j≤i | yes i<m | no ¬j<m = ⊥-elim (¬j<m (begin 
  suc (toℕ j) 
    ≤⟨ s≤s j≤i ⟩ 
  suc (toℕ i) 
    ≤⟨ i<m ⟩ 
  m ∎))
  where open Data.Nat.≤-Reasoning
Three-proof U R L i j j≤i | no ¬p | yes p = refl
Three-proof {m} U R L i j j≤i | no ¬p | no ¬p' = Triangle.proof L (reduce≥ i (≤-pred (≰⇒> ¬p))) (reduce≥ j (≤-pred (≰⇒> ¬p'))) (begin 
  toℕ (reduce≥ j (≤-pred (≰⇒> ¬p'))) 
    ≡⟨ ≡-sym (i∸m≡reduce≥-i-m≤i j (≤-pred (≰⇒> ¬p'))) ⟩ 
  toℕ j ∸ m
    ≤⟨ i≤j⇒i∸k≤j∸k m j≤i ⟩ 
  toℕ i ∸ m
    ≡⟨ i∸m≡reduce≥-i-m≤i i (≤-pred (≰⇒> ¬p)) ⟩ 
  toℕ (reduce≥ i (≤-pred (≰⇒> ¬p))) ∎)
  where open Data.Nat.≤-Reasoning

Three : {m n : ℕ} → Triangle m → Matrix m n → Triangle n → Triangle (m + n)
Three U R L = record { matrix = Four (Triangle.matrix U) R zeroMatrix (Triangle.matrix L); proof = Three-proof U R L }
