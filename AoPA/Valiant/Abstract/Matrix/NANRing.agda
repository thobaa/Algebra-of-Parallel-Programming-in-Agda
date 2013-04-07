open import Algebra.Structures
open import Relation.Binary using (_Preserves₂_⟶_⟶_; IsEquivalence)
open import Data.Product using (_,_)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.Nat using (zero; suc)

import Relation.Binary.EqReasoning as EqR


open import Valiant.Abstract.NonAssociativeNonRing
open import Valiant.Abstract.NonAssociativeNonRing.Structure
module Valiant.Abstract.Matrix.NANRing {l₁ l₂} (NAR : NonAssociativeNonRing l₁ l₂) where

import Valiant.Abstract.Matrix as Matrix
open Matrix NAR
import Valiant.Abstract.Matrix.Operations as Operations
open Operations NAR
import Valiant.Helper.Definitions as Definitions
open Definitions NAR

M+-isCommutativeMonoid : {n : _} → IsCommutativeMonoid (_M≈_ {n} {n}) _+_ zeroMatrix
M+-isCommutativeMonoid = {!!}

-- pf1 : u i' j' == v i' j'
-- vill ha: (x i ∙ (λ k → u k j)) == (y i ∙ 
-- vill ha AC = BD
∙-cong : {n : _} → (_∙_ {n}) Preserves₂ _v≈_ ⟶ _v≈_ ⟶ _R≈_
∙-cong {zero} u≈u' v≈v' = IsEquivalence.refl (NonAssociativeNonRing.isEquivalence NAR)
∙-cong {suc n} {u} {u'} {v} {v'} u≈u' v≈v' = begin 
  u fzero R* v fzero R+ (λ i → u (fsuc i)) ∙ (λ i → v (fsuc i)) 
    ≈⟨ {!!} ⟩ -- addition and multiplication are congruences 
  u' fzero R* v' fzero R+ (λ i → u' (fsuc i)) ∙ (λ i → v' (fsuc i)) ∎
  where open EqR (record { Carrier = R; _≈_ = _R≈_; isEquivalence = NonAssociativeNonRing.isEquivalence NAR })

lemma : {n : _} {A B : Matrix n n} → A M≈ B → (∀ i → A i v≈ B i)
lemma A≈B i j = A≈B i j

lemma2 : {n : _} {A B : Matrix n n} → A M≈ B → (∀ j → (λ k → A k j) v≈ (λ k → B k j))
lemma2 A≈B i j = A≈B j i

M*-cong : {n : _} → (_*_ {n} {n} {n}) Preserves₂ _M≈_ ⟶ _M≈_ ⟶ _M≈_
M*-cong {n} {A} {B} {C} {D} A≈B C≈D i j = ∙-cong (lemma A≈B i) (lemma2 C≈D j)

--M*-cong {suc n} A≈B C≈D fzero fzero = {!!}
--M*-cong {suc n} A≈B C≈D fzero (fsuc i) = {!!}
--M*-cong {suc n} A≈B C≈D (fsuc i) j = {!!}

--_DistributesOverˡ_ : Op₂ A → Op₂ A → Set _
--_*_ DistributesOverˡ _+_ =
--  ∀ x y z → (x * (y + z)) ≈ ((x * y) + (x * z))

--_DistributesOverʳ_ : Op₂ A → Op₂ A → Set _
--_*_ DistributesOverʳ _+_ =
--  ∀ x y z → ((y + z) * x) ≈ ((y * x) + (z * x))

open import Algebra.FunctionProperties using (_DistributesOver_; Zero)
M-distribˡ : {n : _} → (x y z : Matrix n n)→ (x * (y + z)) M≈ ((x * y) + (x * z))
M-distribˡ = {!!}
M-distribʳ : {n : _} → (x y z : Matrix n n)→ ((y + z) * x) M≈ ((y * x) + (z * x))
M-distribʳ = {!!}

M-distrib : {n : _} → _DistributesOver_ (_M≈_ {n} {n}) _*_ _+_
M-distrib = M-distribˡ , M-distribʳ

M-zero : {n : _} → Zero (_M≈_ {n} {n}) zeroMatrix _*_
M-zero = {!!} , {!!}

-- Proof that square Matrices form a NonAssociativeNonRing:
isNonAssociativeNonRing : {n : _} → IsNonAssociativeNonRing (_M≈_ {n} {n}) _+_ _*_ zeroMatrix
isNonAssociativeNonRing = record {
                            +-isCommutativeMonoid = M+-isCommutativeMonoid;
                            *-cong = M*-cong;
                            distrib = M-distrib;
                            zero = M-zero }