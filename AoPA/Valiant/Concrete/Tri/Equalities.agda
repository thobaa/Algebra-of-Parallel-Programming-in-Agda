open import Valiant.Abstract.NonAssociativeNonRing

open import Valiant.Concrete.Splitting
open import Level using (_⊔_)
open import Relation.Binary using (Rel; IsEquivalence; Reflexive; Symmetric; Transitive)
open import Algebra.FunctionProperties

module Valiant.Concrete.Tri.Equalities {l₁ l₂} (NAR : NonAssociativeNonRing l₁ l₂) where

import Valiant.Helper.Definitions
open Valiant.Helper.Definitions NAR

import Valiant.Concrete.Tri
open Valiant.Concrete.Tri NAR
import Valiant.Concrete.Tri.Operations
open Valiant.Concrete.Tri.Operations NAR

import Valiant.Concrete.Mat
open Valiant.Concrete.Mat NAR
import Valiant.Concrete.Mat.Properties
import Valiant.Concrete.Mat.Operations

open Valiant.Concrete.Mat.Operations NAR
open Valiant.Concrete.Mat.Properties NAR
open NonAssociativeNonRing NAR using (_≈_) renaming (refl to ≈refl; sym to ≈sym; trans to ≈trans; +-assoc to R+-assoc; +-comm to R+-comm; +-identity to R+-identity; +-cong to R+-cong; *-cong to R*-cong; distrib to R-distrib; +-commutativeMonoid to R-commutativeMonoid)

-- Equality for Tri, two Tri can only be equal if they have the same splitting.

infix 4 _t≈_
data _t≈_ : ∀ {s'} → Tri s' → Tri s' → Set (l₁ ⊔ l₂) where
  one-eq : one t≈ one
  two-eq : ∀ {s₁ s₂} {U₁ U₂ : Tri s₁} {R₁ R₂ : Mat s₁ s₂} {L₁ L₂ : Tri s₂} → 
           (U₁≈U₂ : U₁ t≈ U₂) → (R₁≈R₂ : R₁ m≈ R₂) → (L₁≈L₂ : L₁ t≈ L₂) → two U₁ R₁ L₁ t≈ two U₂ R₂ L₂

t-refl : ∀ {s} → Reflexive (_t≈_ {s})
t-refl {one}          {one} = one-eq
t-refl {deeper s₁ s₂} {two U R L} = two-eq t-refl m-refl t-refl

t-sym : ∀ {s} → Symmetric (_t≈_ {s})
t-sym one-eq = one-eq
t-sym (two-eq pfU pfR pfL) = two-eq (t-sym pfU) (m-sym pfR) (t-sym pfL)

t-trans : ∀ {s} → Transitive (_t≈_ {s})
t-trans one-eq one-eq = one-eq
t-trans (two-eq pfU pfR pfL) (two-eq pfU' pfR' pfL') = two-eq (t-trans pfU pfU') (m-trans pfR pfR') (t-trans pfL pfL')

t-isEquivalence : ∀ {s} → IsEquivalence (_t≈_ {s})
t-isEquivalence = record
  { refl  = t-refl
  ; sym   = t-sym
  ; trans = t-trans
  }