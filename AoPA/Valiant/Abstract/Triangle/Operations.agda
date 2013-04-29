-- here we put mathematical operations for Triangles

-- TODO
-- add stuff
open import Data.Fin using (Fin; _≤_; toℕ) renaming (zero to fzero; suc to fsuc)
--open import Data.Fin.
open import Data.Product using (proj₁; proj₂)
open import Data.Sum renaming (_⊎_ to _∨_)
open import Data.Nat using (zero; suc; z≤n; s≤s; ≤-pred; decTotalOrder)
open import Data.Nat.Properties using (≰⇒>; n≤1+n)
open import Relation.Nullary using (yes; no)
open import Relation.Binary
--open import Relation.Nullary.Decidable
--Own
open import Valiant.Abstract.NonAssociativeNonRing

module Valiant.Abstract.Triangle.Operations {l₁ l₂} (NAR : NonAssociativeNonRing l₁ l₂) where

import Valiant.Abstract.Matrix as Matrix 
import Valiant.Abstract.Matrix.Operations as MatOp
open MatOp NAR

import Valiant.Abstract.Triangle as Triangle
open Matrix NAR
open Triangle NAR
import Relation.Binary.EqReasoning as EqR
import Relation.Binary.PartialOrderReasoning as POR

open NonAssociativeNonRing NAR using (0#; Carrier; +-cong; +-identity; refl; *-cong; setoid) renaming (_+_ to _R+_; _*_ to _R*_; _≈_ to _R≈_; zero to R-zero)

T+-proof : {n : _} (A B : Triangle n) → (i j : Fin n) → j ≤ i → Triangle.matrix A i j R+ Triangle.matrix B i j R≈ 0#
T+-proof A B i j j≤i = begin 
         Triangle.matrix A i j R+ Triangle.matrix B i j 
           ≈⟨ +-cong (Triangle.proof A i j j≤i) (Triangle.proof B i j j≤i) ⟩  
         0# R+ 0# 
           ≈⟨ proj₁ +-identity 0# ⟩ 
         0# ∎
  where open EqR setoid --(record { Carrier = Carrier; _≈_ = _R≈_; isEquivalence = NonAssociativeNonRing.isEquivalence NAR })

_T+_ : ∀ {n} → Triangle n → Triangle n → Triangle n
A T+ B = record { matrix = Triangle.matrix A + Triangle.matrix B; proof = T+-proof A B}

r*s-zero : (r s : Carrier) → r R≈ 0# ∨ s R≈ 0# → r R* s R≈ 0#
r*s-zero r s (inj₁ r≈0) = begin 
  r R* s 
    ≈⟨ *-cong r≈0 refl ⟩
  0# R* s
    ≈⟨ proj₁ R-zero s ⟩
  0# ∎
  where open EqR setoid --(record { Carrier = Carrier; _≈_ = _R≈_; isEquivalence = NonAssociativeNonRing.isEquivalence NAR })
r*s-zero r s (inj₂ s≈0) = begin 
  r R* s 
    ≈⟨ *-cong refl s≈0 ⟩  
  r R* 0# 
    ≈⟨ proj₂ R-zero r ⟩ 
  0# ∎
  where open EqR setoid --(record { Carrier = Carrier; _≈_ = _R≈_; isEquivalence = NonAssociativeNonRing.isEquivalence NAR })

u∙v-zero : {n : _} (u v : Vector n) → ((i : Fin n) → u i R≈ 0# ∨ v i R≈ 0#) → u ∙ v R≈ 0#
u∙v-zero {zero} u v ui≈0-∨-vi≈0 = refl
u∙v-zero {suc n} u v ui≈0-∨-vi≈0 = begin 
  (head u R* head v) R+ (tail u ∙ tail v)
    ≈⟨ +-cong (r*s-zero (u fzero) (v fzero) (ui≈0-∨-vi≈0 fzero)) (u∙v-zero (tail u) (tail v) (λ i → ui≈0-∨-vi≈0 (fsuc i))) ⟩ 
  0# R+ 0# 
    ≈⟨ proj₁ +-identity 0# ⟩ 
  0# ∎
  where open EqR setoid --(NonAssociativeNonRing.setoid NAR) --(record { Carrier = Carrier; _≈_ = _R≈_; isEquivalence = NonAssociativeNonRing.isEquivalence NAR })

-- should not be here...
_≤?_ : {n : _} → Decidable (_≤_ {n})
fzero ≤? j = yes z≤n
fsuc i ≤? fzero = no (λ ())
fsuc i ≤? fsuc j with i ≤? j
fsuc i ≤? fsuc j | yes p = yes (s≤s p)
fsuc i ≤? fsuc j | no ¬p = no (λ i≤j → ¬p (≤-pred i≤j))

-- antingen är ena noll eller andra.
-- Goal: Triangle.matrix A i ∙ (λ k → Triangle.matrix B k j) R≈ 0#
--Goal: (i' : Fin .n) →
--      Triangle.matrix A i i' R≈ 0# ∨ Triangle.matrix B i' j R≈ 0#
-- Goal: Triangle.matrix A i i' R≈ 0# ∨ Triangle.matrix B i' j R≈ 0#
-- triangel: A i j = 0 om j ≤ i --> (2,1) = 0, (1,1) = 0, (1,2) ≠ 0
Aik≈0-∨-Bkj≈0 : {n : _} → (A B : Triangle n) → (i j : Fin n) → j ≤ i → ((k : Fin n) → Triangle.matrix A i k R≈ 0# ∨ Triangle.matrix B k j R≈ 0#)
Aik≈0-∨-Bkj≈0 A B i j j≤i k with k ≤? i 
Aik≈0-∨-Bkj≈0 A B i j j≤i k | yes k≤i = inj₁ (Triangle.proof A i k k≤i)
Aik≈0-∨-Bkj≈0 A B i j j≤i k | no  k≰i = inj₂ (Triangle.proof B k j (begin 
  toℕ j 
    ≤⟨ j≤i ⟩ 
  toℕ i
    ≤⟨ n≤1+n (toℕ i) ⟩
  suc (toℕ i)
    ≤⟨ ≰⇒> k≰i ⟩
  toℕ k ∎))
  where open Data.Nat.≤-Reasoning


T*-proof : {n : _} (A B : Triangle n) → (i j : Fin n) → j ≤ i → Triangle.matrix A i ∙ (λ k → Triangle.matrix B k j) R≈ 0#
T*-proof A B i j j≤i = u∙v-zero (Triangle.matrix A i) (λ k → Triangle.matrix B k j) (Aik≈0-∨-Bkj≈0 A B i j j≤i)

_T*_ : ∀ {n} → Triangle n → Triangle n → Triangle n
A T* B = record { matrix = Triangle.matrix A * Triangle.matrix B; proof = T*-proof A B }

_T≈_ : ∀ {n} → Triangle n → Triangle n → Set l₂
A T≈ B = Triangle.matrix A M≈ Triangle.matrix B