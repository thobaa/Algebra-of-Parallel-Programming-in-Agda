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

-- equality, only equal if have same splitting.

infix 4 _t≈_
data _t≈_ : ∀ {s'} → Tri s' → Tri s' → Set (l₁ ⊔ l₂) where
  one-eq : one t≈ one
  two-eq : ∀ {s₁ s₂} {U₁ U₂ : Tri s₁} {R₁ R₂ : Mat s₁ s₂} {L₁ L₂ : Tri s₂} → 
           (U₁≈U₂ : U₁ t≈ U₂) → (R₁≈R₂ : R₁ m≈ R₂) → (L₁≈L₂ : L₁ t≈ L₂) → two U₁ R₁ L₁ t≈ two U₂ R₂ L₂

{-
reflV : ∀ {s} → Reflexive (_v≈_ {s})
--reflV {one} {one x} = one-eq ≈refl
--reflV {(deeper s₁ s₂)} {two y y'} = two-eq reflV reflV

reflM : ∀ {s₁ s₂} → Reflexive (_m≈_ {s₁} {s₂})
reflM {one} {one} {Sing x} = Sing-eq ≈refl
reflM {one} {(deeper s₁ s₂)} {RVec y} = RVec-eq reflV
reflM {(deeper s₁ s₂)} {one} {CVec y} = CVec-eq reflV
reflM {(deeper r₁ r₂)} {(deeper c₁ c₂)} {quad A B C D} = quad-eq reflM reflM reflM reflM
-}
t-refl : ∀ {s} → Reflexive (_t≈_ {s})
t-refl {one}          {one} = one-eq
t-refl {deeper s₁ s₂} {two U R L} = two-eq t-refl m-refl t-refl
{-
symV : ∀ {s} → Symmetric (_v≈_ {s})
symV (one-eq pf) = one-eq (≈sym pf)
symV (two-eq pf₁ pf₂) = two-eq (symV pf₁) (symV pf₂)

symM : ∀ {s₁ s₂} → Symmetric (_m≈_ {s₁} {s₂})
symM (Sing-eq pf) = Sing-eq (≈sym pf)
symM (CVec-eq pf) = CVec-eq (symV pf)
symM (RVec-eq pf) = RVec-eq (symV pf)
symM (quad-eq pf₁ pf₂ pf₃ pf₄) = quad-eq (symM pf₁) (symM pf₂) (symM pf₃) (symM pf₄)
-}
t-sym : ∀ {s} → Symmetric (_t≈_ {s})
t-sym one-eq = one-eq
t-sym (two-eq pfU pfR pfL) = two-eq (t-sym pfU) (m-sym pfR) (t-sym pfL)
  --sym' --{deeper s₁ s₂} (two-eq pfU pfR pfL) = two-eq (sym' pfU) (symM pfR) (sym' pfL)
{-
transV : ∀ {s} → Transitive (_v≈_ {s})
transV (one-eq pf₁) (one-eq pf₂) = one-eq (≈trans pf₁ pf₂)
transV (two-eq pf₁ pf₂) (two-eq pf₃ pf₄) = two-eq (transV pf₁ pf₃) (transV pf₂ pf₄)
transM : ∀ {s₁ s₂} → Transitive (_m≈_ {s₁} {s₂})
transM (Sing-eq pf₁) (Sing-eq pf₂) = Sing-eq (≈trans pf₁ pf₂)
transM (RVec-eq pf₁) (RVec-eq pf₂) = RVec-eq (transV pf₁ pf₂)
transM (CVec-eq pf₁) (CVec-eq pf₂) = CVec-eq (transV pf₁ pf₂)
transM (quad-eq pf₁ pf₂ pf₃ pf₄) (quad-eq pf₁' pf₂' pf₃' pf₄') = quad-eq (transM pf₁ pf₁') (transM pf₂ pf₂') (transM pf₃ pf₃') (transM pf₄ pf₄')
-}
t-trans : ∀ {s} → Transitive (_t≈_ {s})
t-trans one-eq one-eq = one-eq
t-trans (two-eq pfU pfR pfL) (two-eq pfU' pfR' pfL') = two-eq (t-trans pfU pfU') (m-trans pfR pfR') (t-trans pfL pfL')

t-isEquivalence : ∀ {s} → IsEquivalence (_t≈_ {s})
t-isEquivalence = record
  { refl  = t-refl
  ; sym   = t-sym
  ; trans = t-trans
  }

{-
isEquivalenceM : ∀ {s₁ s₂ : Splitting} → IsEquivalence (_m≈_ {s₁} {s₂})
isEquivalenceM = record 
  { refl = reflM
  ; sym = symM
  ; trans = transM }

isEquivalenceV : ∀ {s} → IsEquivalence (_v≈_ {s})
isEquivalenceV = record
  { refl  = reflV
  ; sym   = symV
  ; trans = transV
  }-}