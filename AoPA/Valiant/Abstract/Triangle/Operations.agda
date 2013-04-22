-- here we put mathematical operations for Triangles

-- TODO
-- add stuff
open import Data.Fin using (Fin; _≤_)
open import Data.Product using (proj₁; proj₂)
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

open NonAssociativeNonRing NAR renaming (_+_ to _R+_; _*_ to _R*_; _≈_ to _R≈_)

T+-proof : {n : _} (A B : Triangle n) → (i j : Fin n) → j ≤ i → Triangle.matrix A i j R+ Triangle.matrix B i j R≈ 0#
T+-proof A B i j j≤i = begin 
         Triangle.matrix A i j R+ Triangle.matrix B i j 
           ≈⟨ +-cong (Triangle.proof A i j j≤i) (Triangle.proof B i j j≤i) ⟩  
         0# R+ 0# 
           ≈⟨ proj₁ +-identity 0# ⟩ 
         0# ∎
  where open EqR (record { Carrier = Carrier; _≈_ = _R≈_; isEquivalence = NonAssociativeNonRing.isEquivalence NAR })

_T+_ : ∀ {n} → Triangle n → Triangle n → Triangle n
A T+ B = record { matrix = Triangle.matrix A + Triangle.matrix B; proof = T+-proof A B}


-- antingen är ena noll eller andra.
T*-proof : {n : _} (A B : Triangle n) → (i j : Fin n) → j ≤ i → Triangle.matrix A i ∙ (λ k → Triangle.matrix B k j) R≈ 0#
T*-proof A B i j j≤i = {!!}

_T*_ : ∀ {n} → Triangle n → Triangle n → Triangle n
A T* B = record { matrix = Triangle.matrix A * Triangle.matrix B; proof = T*-proof A B }

_T≈_ : ∀ {n} → Triangle n → Triangle n → Set l₂
A T≈ B = Triangle.matrix A M≈ Triangle.matrix B