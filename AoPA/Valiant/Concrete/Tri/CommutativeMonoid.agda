open import Valiant.Abstract.NonAssociativeNonRing
open import Algebra
open import Algebra.Structures
open import Data.Product using (proj₁; Σ; _,_)

module Valiant.Concrete.Tri.CommutativeMonoid {l₁ l₂} (NAR : NonAssociativeNonRing l₁ l₂) where


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

open NonAssociativeNonRing NAR using (_≈_) renaming (refl to ≈refl; sym to ≈sym; trans to ≈trans; +-assoc to R+-assoc; +-comm to R+-comm; +-identity to R+-identity; +-cong to R+-cong; *-cong to R*-cong; distrib to R-distrib; +-commutativeMonoid to R-commutativeMonoid)


assocV : ∀ {s} → (x y z : Vec s) → (x ⊕ y) ⊕ z v≈ x ⊕ (y ⊕ z)
assocV (one x) (one y) (one z) = one-eq (R+-assoc x y z)
assocV (two u₁ v₁) (two u₂ v₂) (two u₃ v₃) = two-eq (assocV u₁ u₂ u₃) (assocV v₁ v₂ v₃)

assocM : ∀ {s₁ s₂} → (x y z : Mat s₁ s₂) → (x + y) + z m≈ x + (y + z)
assocM (Sing x) (Sing y) (Sing z) = Sing-eq (R+-assoc x y z)
assocM (RVec x) (RVec y) (RVec z) = RVec-eq (assocV x y z)
assocM (CVec x) (CVec y) (CVec z) = CVec-eq (assocV x y z)
assocM (quad A₁ B₁ C₁ D₁) (quad A₂ B₂ C₂ D₂) (quad A₃ B₃ C₃ D₃) = quad-eq (assocM A₁ A₂ A₃) (assocM B₁ B₂ B₃) (assocM C₁ C₂ C₃) (assocM D₁ D₂ D₃)

assocT : ∀ {s} → (x y z : Tri s) → (x ◂+ y) ◂+ z t≈ x ◂+ (y ◂+ z)
assocT one one one = one-eq
assocT (two U₁ R₁ L₁) (two U₂ R₂ L₂) (two U₃ R₃ L₃) = two-eq (assocT U₁ U₂ U₃) (assocM R₁ R₂ R₃) (assocT L₁ L₂ L₃)

commV : ∀ {s} → (x y : Vec s) → x ⊕ y v≈ y ⊕ x
commV (one x) (one y) = one-eq (R+-comm x y)
commV (two u₁ v₁) (two u₂ v₂) = two-eq (commV u₁ u₂) (commV v₁ v₂)
commM : ∀ {s₁ s₂} → (x y : Mat s₁ s₂) → x + y m≈ y + x
commM (Sing x) (Sing y) = Sing-eq (R+-comm x y)
commM (RVec u) (RVec v) = RVec-eq (commV u v)
commM (CVec u) (CVec v) = CVec-eq (commV u v)
commM (quad A₁ B₁ C₁ D₁) (quad A₂ B₂ C₂ D₂) = quad-eq (commM A₁ A₂) (commM B₁ B₂) (commM C₁ C₂) (commM D₁ D₂)

commT : ∀ {s} → (x y : Tri s) → x ◂+ y t≈ y ◂+ x
commT one one = one-eq
commT (two U₁ R₁ L₁) (two U₂ R₂ L₂) = two-eq (commT U₁ U₂) (commM R₁ R₂) (commT L₁ L₂)
  
identityˡV : ∀ {s} → (x : Vec s) → zeroVec ⊕ x v≈ x 
identityˡV (one x) = one-eq (proj₁ R+-identity x)
identityˡV (two u v) = two-eq (identityˡV u) (identityˡV v)
identityˡM : ∀ {s₁ s₂} → (x : Mat s₁ s₂) → zeroMat + x m≈ x 
identityˡM (Sing x) = Sing-eq (proj₁ R+-identity x)
identityˡM (RVec u) = RVec-eq (identityˡV u)
identityˡM (CVec u) = CVec-eq (identityˡV u)
identityˡM (quad A B C D) = quad-eq (identityˡM A) (identityˡM B) (identityˡM C) (identityˡM D)

identityˡT : ∀ {s} → (x : Tri s) → zeroTri ◂+ x t≈ x 
identityˡT one = one-eq
identityˡT (two U R L) = two-eq (identityˡT U) (identityˡM R) (identityˡT L)
  

isSemigroup : ∀ {s} → IsSemigroup _t≈_ (_◂+_ {s})
isSemigroup = record 
  { isEquivalence = isEquivalenceT
  ; assoc         = assocT
  ; ∙-cong        = ◂+-cong
  }

isSemigroupM : ∀ {s₁ s₂} → IsSemigroup _m≈_ (_+_ {s₁} {s₂})
isSemigroupM = record 
  { isEquivalence = isEquivalenceM
  ; assoc = assocM
  ; ∙-cong = +-cong }

isSemigroupV : ∀ {s} → IsSemigroup _v≈_ (_⊕_ {s})
isSemigroupV = record 
  { isEquivalence = isEquivalenceV
  ; assoc         = assocV
  ; ∙-cong        = ⊕-cong
  }

isCommutativeMonoid : ∀ {s} → IsCommutativeMonoid _t≈_ (_◂+_ {s}) zeroTri
isCommutativeMonoid = record 
  { isSemigroup = isSemigroup
  ; identityˡ   = identityˡT
  ; comm        = commT
  }
isCommutativeMonoidM : ∀ {s₁ s₂} → IsCommutativeMonoid _m≈_ (_+_ {s₁} {s₂}) zeroMat
isCommutativeMonoidM = record 
  { isSemigroup = isSemigroupM
  ; identityˡ   = identityˡM
  ; comm        = commM
  }
isCommutativeMonoidV : ∀ {s} → IsCommutativeMonoid _v≈_ (_⊕_ {s}) zeroVec
isCommutativeMonoidV = record 
  { isSemigroup = isSemigroupV
  ; identityˡ   = identityˡV
  ; comm        = commV
  }

commutativeMonoid : ∀ {s} → CommutativeMonoid _ _
commutativeMonoid {s} = record
  { Carrier             = Tri s
  ; _≈_                 = _t≈_
  ; _∙_                 = _◂+_
  ; ε                   = zeroTri
  ; isCommutativeMonoid = isCommutativeMonoid
  }

commutativeMonoidM : ∀ {s₁} {s₂} → CommutativeMonoid _ _
commutativeMonoidM {s₁} {s₂} = record
  { Carrier             = Mat s₁ s₂
  ; _≈_                 = _m≈_
  ; _∙_                 = _+_
  ; ε                   = zeroMat
  ; isCommutativeMonoid = isCommutativeMonoidM
  }
commutativeMonoidV : ∀ {s} → CommutativeMonoid _ _
commutativeMonoidV {s} = record
  { Carrier             = Vec s
  ; _≈_                 = _v≈_
  ; _∙_                 = _⊕_
  ; ε                   = zeroVec
  ; isCommutativeMonoid = isCommutativeMonoidV
  }

