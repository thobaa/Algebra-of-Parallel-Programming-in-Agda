open import Valiant.Abstract.NonAssociativeNonRing
open import Valiant.Abstract.NonAssociativeNonRing.Structure
open import Algebra
open import Algebra.Structures
import Algebra.FunctionProperties
open import Relation.Binary.PropositionalEquality as PE
  using ()--_≡_; refl; sym; cong; cong₂)

open import Level using (_⊔_)

open import Relation.Binary using (Rel; IsEquivalence; Setoid; Reflexive; Symmetric; Transitive)
import Relation.Binary.EqReasoning as EqR
open import Data.Product using (proj₁; Σ; _,_)

open import Valiant.Concrete.Splitting

module Valiant.Concrete.Tri.Properties {l₁ l₂} (NAR : NonAssociativeNonRing l₁ l₂) where

--s : Splitting
--s = deeper s₁ s₂

import Valiant.Helper.Definitions
open Valiant.Helper.Definitions NAR

import Valiant.Concrete.Tri
open Valiant.Concrete.Tri NAR
import Valiant.Concrete.Tri.Operations
open Valiant.Concrete.Tri.Operations NAR

import Valiant.Concrete.Mat
open Valiant.Concrete.Mat NAR
import Valiant.Concrete.Mat.Operations
open Valiant.Concrete.Mat.Operations NAR

import Valiant.Concrete.Tri.Equalities 
open Valiant.Concrete.Tri.Equalities NAR
import Valiant.Concrete.Tri.Congruences 
open Valiant.Concrete.Tri.Congruences NAR
import Valiant.Concrete.Tri.CommutativeMonoid
open Valiant.Concrete.Tri.CommutativeMonoid NAR
import Valiant.Concrete.Tri.Distributivities
open Valiant.Concrete.Tri.Distributivities NAR
import Valiant.Concrete.Tri.Zeros
open Valiant.Concrete.Tri.Zeros NAR

setoidM : ∀ {s₁ s₂} → Setoid l₁ (l₂ ⊔ l₁)
setoidM {s₁} {s₂} = record { Carrier = Mat s₁ s₂; _≈_ = _m≈_; isEquivalence = isEquivalenceM }



open NonAssociativeNonRing NAR using (_≈_) renaming (refl to ≈refl; sym to ≈sym; trans to ≈trans; +-assoc to R+-assoc; +-comm to R+-comm; +-identity to R+-identity; +-cong to R+-cong; --+-idempotent to R+-idempotent; 
  *-cong to R*-cong; distrib to R-distrib; +-commutativeMonoid to R-commutativeMonoid)



--open Algebra.FunctionProperties (_t≈_  {s})




-- left to do: also, clean things up by giving proper names "Associative" etc 
-- think about ∀ s, should probably not parametrize by it.
{-private 
  
  -- idempotent stuff
  ⊕-idempotent : ∀ {s} (x : Vec s) → x ⊕ x v≈ x
  ⊕-idempotent (Valiant.Concrete.Mat.one x) = Valiant.Concrete.Tri.Equalities.one-eq (R+-idempotent x)
  ⊕-idempotent (Valiant.Concrete.Mat.two u v) = Valiant.Concrete.Tri.Equalities.two-eq (⊕-idempotent u) (⊕-idempotent v)
  +-idempotent : ∀ {s₁ s₂} (x : Mat s₁ s₂) → x + x m≈ x
  +-idempotent (Valiant.Concrete.Mat.Sing x) = Valiant.Concrete.Tri.Equalities.Sing-eq (R+-idempotent x)
  +-idempotent (Valiant.Concrete.Mat.RVec v) = Valiant.Concrete.Tri.Equalities.RVec-eq (⊕-idempotent v)
  +-idempotent (Valiant.Concrete.Mat.CVec v) = Valiant.Concrete.Tri.Equalities.CVec-eq (⊕-idempotent v)
  +-idempotent (Valiant.Concrete.Mat.quad A B C D) = Valiant.Concrete.Tri.Equalities.quad-eq (+-idempotent A) (+-idempotent B) (+-idempotent C) (+-idempotent D)
  ◂+-idempotent : ∀ {s} (x : Tri s) → x ◂+ x t≈ x
  ◂+-idempotent Valiant.Concrete.Tri.one = Valiant.Concrete.Tri.Equalities.one-eq
  ◂+-idempotent (Valiant.Concrete.Tri.two U R L) = Valiant.Concrete.Tri.Equalities.two-eq (◂+-idempotent U) (+-idempotent R) (◂+-idempotent L)
  -}

isNonAssociativeNonRing : ∀ {s} → IsNonAssociativeNonRing _t≈_ (_◂+_ {s}) (_◂_ {s}) zeroTri
isNonAssociativeNonRing = record 
  { +-isCommutativeMonoid = isCommutativeMonoid
  --; +-idempotent = ◂+-idempotent
  ; *-cong = ◂-cong
  ; distrib = ◂-distrib
  ; zero = ◂-zeroˡ , ◂-zeroʳ
  }

isNonAssociativeNonRingM : ∀ {s} → IsNonAssociativeNonRing _m≈_ (_+_ {s} {s}) (_*_) zeroMat
isNonAssociativeNonRingM = record 
  { +-isCommutativeMonoid = isCommutativeMonoidM
  --; +-idempotent = +-idempotent
  ; *-cong = *-cong
  ; distrib = *-distribˡ , (λ x y z → *-distribʳ y z x)
  ; zero = *-zeroˡ , *-zeroʳ 
  }