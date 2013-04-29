-- here we put mathematical operations for matrixes and vectors.

-- TODO 
-- * scalar multiplication
-- * pointwise multiplication.

open import Data.Nat using (ℕ; zero; suc)
open import Data.Vec using (Vec; []; _∷_; foldr; map; zip; reverse)
open import Function using (_∘_; id)
open import Data.Product using (uncurry; uncurry′; <_,_>; proj₂)
open import Data.Fin using () renaming (zero to f0; suc to fsuc)


open import Valiant.Abstract.NonAssociativeNonRing
module Valiant.Abstract.Matrix.Operations {l₁ l₂} (NAR : NonAssociativeNonRing l₁ l₂) where

import Valiant.Helper.Definitions
open Valiant.Helper.Definitions NAR using ()

import Valiant.Abstract.Matrix as Matrix
open Matrix NAR

open NonAssociativeNonRing NAR renaming (zero to R-zero; _+_ to _R+_; _*_ to _R*_; _≈_ to _R≈_; +-identity to R+-identity; sym to R-sym; trans to R-trans)

-- Dot product
infix 7 _∙_
_∙_ : ∀ {n} → Vector n → Vector n → Carrier
_∙_ {zero} u v = 0# -- this is bad, because it adds an extra zero always.
_∙_ {suc n} u v = (u f0 R* v f0) R+ _∙_ {n} (λ i → u (fsuc i)) (λ i → v (fsuc i))

trans-∙ : {x y : Carrier} → x R≈ y → x R≈ y R+ 0#
trans-∙ x≈y = R-trans x≈y (R-sym (proj₂ R+-identity _))

-- Exterior product
infix 7 _⊗_
_⊗_ : {n m : ℕ} → Vector n → Vector m → Matrix n m 
_⊗_ u v i j = u i R* v j

-- Multiplication by Scalar
infix 7 _sV*_
_sV*_ : {n : ℕ} → Carrier → Vector n → Vector n 
_sV*_ x v i = x R* v i

_Vs*_ : {n : ℕ} → Vector n → Carrier → Vector n
_Vs*_ v x i = v i R* x

infix 6 _V+_
_V+_ : ∀ {n} → Vector n → Vector n → Vector n
u V+ v = λ i → u i R+ v i

-- Vector equality
infix 4 _V≈_
_V≈_ : ∀ {n} → Vector n → Vector n → Set l₂
u V≈ v = (i : _) → u i R≈ v i


-- Matrix addition
infix 6 _+_
_+_ : ∀ {m n} -> Matrix m n -> Matrix m n -> Matrix m n
_+_ A B = λ i j → (A i j) R+ (B i j)

-- Matrix multiplication
infix 7 _*_
_*_ : ∀ {m n p} → Matrix m n → Matrix n p → Matrix m p
A * B = λ i j → (λ k → A i k) ∙ (λ k → B k j)

-- Non-associative powers
_^[1+_] : ∀ {n} → Matrix n n → ℕ → Matrix n n
_^[1+_] {n} A i = (foldr (λ _ → Matrix n n) _+_ A ∘ (map (uncurry (_*_))) ∘ (uncurry′ zip) ∘ < id , reverse >) (allPrevious i)
  where
    allPrevious : (k : ℕ) -> Vec (Matrix n n) k
    allPrevious zero     = []
    allPrevious (suc n') = A ^[1+ n' ] ∷ allPrevious n'

infix 4 _M≈_
_M≈_ : ∀ {m n} → Matrix m n → Matrix m n → Set l₂
A M≈ B = (i : _) (j : _) → A i j R≈ B i j