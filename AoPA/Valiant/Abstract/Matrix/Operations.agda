-- here we put mathematical operations for matrixes and vectors.

-- TODO 
-- * scalar multiplication
-- * pointwise multiplication.

open import Data.Nat using (ℕ; zero; suc)
open import Data.Vec using (Vec; []; _∷_; foldr; map; zip; reverse)
open import Function using (_∘_; id)
open import Data.Product using (uncurry; uncurry′; <_,_>)
open import Data.Fin using () renaming (zero to f0; suc to fsuc)


open import Valiant.Abstract.NonAssociativeNonRing
module Valiant.Abstract.Matrix.Operations {l₁ l₂} (NAR : NonAssociativeNonRing l₁ l₂) where

import Valiant.Helper.Definitions
open Valiant.Helper.Definitions NAR

import Valiant.Abstract.Matrix as Matrix
open Matrix NAR

-- Dot product
_∙_ : ∀ {n} → Vector n → Vector n → R
_∙_ {zero} u v = R0
_∙_ {suc n} u v = (u f0 R* v f0) R+ _∙_ {n} (λ i → u (fsuc i)) (λ i → v (fsuc i))

_v+_ : ∀ {n} → Vector n → Vector n → Vector n
u v+ v = λ i → u i R+ v i

-- Vector equality
_v≈_ : ∀ {n} → Vector n → Vector n → Set l₂
u v≈ v = (i : _) → u i R≈ v i


-- Matrix addition
_+_ : ∀ {m n} -> Matrix m n -> Matrix m n -> Matrix m n
_+_ A B = λ i j → (A i j) R+ (B i j)

-- Matrix multiplication
_*_ : ∀ {m n p} → Matrix m n → Matrix n p → Matrix m p
A * B = λ i j → (λ k → A i k) ∙ (λ k → B k j)

-- Non-associative powers
_^[1+_] : ∀ {n} → Matrix n n → ℕ → Matrix n n
_^[1+_] {n} A i = (foldr (λ _ → Matrix n n) _+_ A ∘ (map (uncurry (_*_))) ∘ (uncurry′ zip) ∘ < id , reverse >) (allPrevious i)
  where
    allPrevious : (k : ℕ) -> Vec (Matrix n n) k
    allPrevious zero     = []
    allPrevious (suc n') = A ^[1+ n' ] ∷ allPrevious n'

_M≈_ : ∀ {m n} → Matrix m n → Matrix m n → Set l₂
A M≈ B = (i : _) (j : _) → A i j R≈ B i j