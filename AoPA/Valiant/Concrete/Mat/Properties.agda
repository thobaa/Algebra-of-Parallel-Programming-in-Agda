open import Valiant.Abstract.NonAssociativeNonRing
open import Valiant.Abstract.NonAssociativeNonRing.Structure
open import Algebra
open import Algebra.Structures
import Algebra.FunctionProperties
--open import Relation.Binary.PropositionalEquality as PE
--  using ()--_≡_; refl; sym; cong; cong₂)

open import Relation.Binary using (Rel; IsEquivalence; Setoid)
import Relation.Binary.EqReasoning as EqR
open import Data.Product using (proj₁; Σ; _,_)

open import Valiant.Concrete.Splitting

module Valiant.Concrete.Mat.Properties {l₁ l₂} (NAR : NonAssociativeNonRing l₁ l₂) where

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

open import Level

open NonAssociativeNonRing NAR using (_≈_) renaming (_+_ to _R+_; refl to ≈refl; sym to ≈sym; trans to ≈trans; +-assoc to R+-assoc; +-comm to R+-comm; +-identity to R+-identity; +-cong to R+-cong; *-cong to R*-cong; distrib to R-distrib)



v-refl : ∀ {s₁} → {x : Vec s₁} → x v≈ x
v-refl {one} {one x} = one-eq ≈refl
v-refl {(deeper s₁ s₂)} {two y y'} = two-eq v-refl v-refl
m-refl : ∀ {s₁ s₂} → {x : Mat s₁ s₂} → x m≈ x
m-refl {one} {one} {Sing x} = Sing-eq ≈refl
m-refl {one} {(deeper s₁ s₂)} {RVec y} = RVec-eq v-refl
m-refl {(deeper s₁ s₂)} {one} {CVec y} = CVec-eq v-refl
m-refl {(deeper r₁ r₂)} {(deeper c₁ c₂)} {quad A B C D} = quad-eq m-refl m-refl m-refl m-refl

v-sym : ∀ {s} → {i j : Vec s} → i v≈ j → j v≈ i
v-sym (one-eq pf) = one-eq (≈sym pf)
v-sym (two-eq pf₁ pf₂) = two-eq (v-sym pf₁) (v-sym pf₂)
m-sym : ∀ {s₁ s₂} → {i j : Mat s₁ s₂} → i m≈ j → j m≈ i
m-sym (Sing-eq pf) = Sing-eq (≈sym pf)
m-sym (CVec-eq pf) = CVec-eq (v-sym pf)
m-sym (RVec-eq pf) = RVec-eq (v-sym pf)
m-sym (quad-eq pf₁ pf₂ pf₃ pf₄) = quad-eq (m-sym pf₁) (m-sym pf₂) (m-sym pf₃) (m-sym pf₄)

  
v-trans : ∀ {s} → {i j k : Vec s} → i v≈ j → j v≈ k → i v≈ k
v-trans (one-eq pf₁) (one-eq pf₂) = one-eq (≈trans pf₁ pf₂)
v-trans (two-eq pf₁ pf₂) (two-eq pf₃ pf₄) = two-eq (v-trans pf₁ pf₃) (v-trans pf₂ pf₄)
m-trans : ∀ {s₁ s₂} → {i j k : Mat s₁ s₂} → i m≈ j → j m≈ k → i m≈ k
m-trans (Sing-eq pf₁) (Sing-eq pf₂) = Sing-eq (≈trans pf₁ pf₂)
m-trans (RVec-eq pf₁) (RVec-eq pf₂) = RVec-eq (v-trans pf₁ pf₂)
m-trans (CVec-eq pf₁) (CVec-eq pf₂) = CVec-eq (v-trans pf₁ pf₂)
m-trans (quad-eq pf₁ pf₂ pf₃ pf₄) (quad-eq pf₁' pf₂' pf₃' pf₄') = quad-eq (m-trans pf₁ pf₁') (m-trans pf₂ pf₂') (m-trans pf₃ pf₃') (m-trans pf₄ pf₄')

  
v-isEquivalence : ∀ {s} → IsEquivalence (_v≈_ {s})
v-isEquivalence = record
  { refl  = v-refl
  ; sym   = v-sym
  ; trans = v-trans
  }


m-isEquivalence : ∀ {s₁ s₂ : Splitting} → IsEquivalence (_m≈_ {s₁} {s₂})
m-isEquivalence = record 
  { refl = m-refl
  ; sym = m-sym
  ; trans = m-trans }

-- not to be here
m-setoid : ∀ {s₁ s₂} → Setoid l₁ (l₂ ⊔ l₁)
m-setoid {s₁} {s₂} = record { Carrier = Mat s₁ s₂; _≈_ = _m≈_; isEquivalence = m-isEquivalence }

  
assocV : {s : Splitting} → (x y z : Vec s) → (x ⊕ y) ⊕ z v≈ x ⊕ (y ⊕ z)
assocV (one x) (one y) (one z) = one-eq (R+-assoc x y z)
assocV (two u₁ v₁) (two u₂ v₂) (two u₃ v₃) = two-eq (assocV u₁ u₂ u₃) (assocV v₁ v₂ v₃)

assocM : {s₁ s₂ : Splitting} → (x y z : Mat s₁ s₂) → (x + y) + z m≈ x + (y + z)
assocM (Sing x) (Sing y) (Sing z) = Sing-eq (R+-assoc x y z)
assocM (RVec x) (RVec y) (RVec z) = RVec-eq (assocV x y z)
assocM (CVec x) (CVec y) (CVec z) = CVec-eq (assocV x y z)
assocM (quad A₁ B₁ C₁ D₁) (quad A₂ B₂ C₂ D₂) (quad A₃ B₃ C₃ D₃) = quad-eq (assocM A₁ A₂ A₃) (assocM B₁ B₂ B₃) (assocM C₁ C₂ C₃) (assocM D₁ D₂ D₃)

  
commV : ∀ {s} → (x y : Vec s) → x ⊕ y v≈ y ⊕ x
commV (one x) (one y) = one-eq (R+-comm x y)
commV (two u₁ v₁) (two u₂ v₂) = two-eq (commV u₁ u₂) (commV v₁ v₂)
commM : ∀ {s₁ s₂} → (x y : Mat s₁ s₂) → x + y m≈ y + x
commM (Sing x) (Sing y) = Sing-eq (R+-comm x y)
commM (RVec u) (RVec v) = RVec-eq (commV u v)
commM (CVec u) (CVec v) = CVec-eq (commV u v)
commM (quad A₁ B₁ C₁ D₁) (quad A₂ B₂ C₂ D₂) = quad-eq (commM A₁ A₂) (commM B₁ B₂) (commM C₁ C₂) (commM D₁ D₂)


identityˡV : ∀ {s} → (x : Vec s) → zeroVec ⊕ x v≈ x 
identityˡV (one x) = one-eq (proj₁ R+-identity x)
identityˡV (two u v) = two-eq (identityˡV u) (identityˡV v)
identityˡM : ∀ {s₁ s₂} → (x : Mat s₁ s₂) → zeroMat + x m≈ x 
identityˡM (Sing x) = Sing-eq (proj₁ R+-identity x)
identityˡM (RVec u) = RVec-eq (identityˡV u)
identityˡM (CVec u) = CVec-eq (identityˡV u)
identityˡM (quad A B C D) = quad-eq (identityˡM A) (identityˡM B) (identityˡM C) (identityˡM D)

⊕-cong : ∀ {s} {x y u v : Vec s} → x v≈ y → u v≈ v → x ⊕ u v≈ y ⊕ v
⊕-cong (one-eq pf₁) (one-eq pf₂) = one-eq (R+-cong pf₁ pf₂)
⊕-cong (two-eq pf₁ pf₂) (two-eq pf₃ pf₄) = two-eq (⊕-cong pf₁ pf₃) (⊕-cong pf₂ pf₄)

+-cong : ∀ {s₁ s₂} {x y u v : Mat s₁ s₂} → x m≈ y → u m≈ v → x + u m≈ y + v
+-cong (Sing-eq pf₁) (Sing-eq pf₂) = Sing-eq (R+-cong pf₁ pf₂)
+-cong (RVec-eq pf₁) (RVec-eq pf₂) = RVec-eq (⊕-cong pf₁ pf₂)
+-cong (CVec-eq pf₁) (CVec-eq pf₂) = CVec-eq (⊕-cong pf₁ pf₂)
+-cong (quad-eq pf₁ pf₂ pf₃ pf₄) (quad-eq pf₁' pf₂' pf₃' pf₄') = quad-eq (+-cong pf₁ pf₁') (+-cong pf₂ pf₂') (+-cong pf₃ pf₃') (+-cong pf₄ pf₄')

isSemigroupM : ∀ {s₁ s₂} → IsSemigroup _m≈_ (_+_ {s₁} {s₂})
isSemigroupM = record 
  { isEquivalence = m-isEquivalence
  ; assoc = assocM
  ; ∙-cong = +-cong }

isSemigroupV : ∀ {s} → IsSemigroup _v≈_ (_⊕_ {s})
isSemigroupV = record 
  { isEquivalence = v-isEquivalence
  ; assoc         = assocV
  ; ∙-cong        = ⊕-cong
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



commutativeMonoid : ∀ {s₁} {s₂} → CommutativeMonoid _ _
commutativeMonoid {s₁} {s₂} = record
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

    

-- "vector space related stuff"
⊛|-cong : ∀ {s} {x y : R} {u v : Vec s} → x ≈ y → u v≈ v → x ⊛| u v≈ y ⊛| v
⊛|-cong pf₁ (one-eq pf₂) = one-eq (R*-cong pf₁ pf₂)
⊛|-cong pf₁ (two-eq pf₂ pf₃) = two-eq (⊛|-cong pf₁ pf₂) (⊛|-cong pf₁ pf₃)

|⊛-cong : ∀ {s} {x y : Vec s}{u v : R}  → x v≈ y → u ≈ v → x |⊛ u v≈ y |⊛ v
|⊛-cong (one-eq pf₁) pf₂ = one-eq (R*-cong pf₁ pf₂)
|⊛-cong (two-eq pf₁ pf₂) pf₃ = two-eq (|⊛-cong pf₁ pf₃) (|⊛-cong pf₂ pf₃)

  -- exterior product
⊛-cong : ∀ {s₁ s₂} {x y : Vec s₁}{u v : Vec s₂}  → x v≈ y → u v≈ v → x ⊛ u m≈ y ⊛ v
⊛-cong (one-eq pf₁) (one-eq pf₂) = Sing-eq (R*-cong pf₁ pf₂)
⊛-cong (one-eq pf₁) (two-eq pf₂ pf₃) = RVec-eq (two-eq (⊛|-cong pf₁ pf₂) (⊛|-cong pf₁ pf₃))
⊛-cong (two-eq pf₁ pf₂) (one-eq pf₃) = CVec-eq (two-eq (|⊛-cong pf₁ pf₃) (|⊛-cong pf₂ pf₃))
⊛-cong (two-eq pf₁ pf₂) (two-eq pf₃ pf₄) = quad-eq (⊛-cong pf₁ pf₃) (⊛-cong pf₁ pf₄) (⊛-cong pf₂ pf₃) (⊛-cong pf₂ pf₄)
  
∙-cong' : ∀ {s} {x y u v : Vec s} → x v≈ y → u v≈ v → x ∙ u ≈ y ∙ v
∙-cong' (one-eq pf₁) (one-eq pf₂) = R*-cong pf₁ pf₂
∙-cong' (two-eq pf₁ pf₂) (two-eq pf₃ pf₄) = R+-cong (∙-cong' pf₁ pf₃) (∙-cong' pf₂ pf₄)

|*-cong : ∀ {s₁ s₂} {x y : Vec s₁}{u v : Mat s₁ s₂} → x v≈ y → u m≈ v → x |* u v≈ y |* v
|*-cong (one-eq pf₁) (Sing-eq pf₂) = one-eq (R*-cong pf₁ pf₂)
|*-cong (one-eq pf₁) (RVec-eq (two-eq pf₂ pf₃)) = two-eq (⊛|-cong pf₁ pf₂) (⊛|-cong pf₁ pf₃)
|*-cong (two-eq pf₁ pf₂) (CVec-eq (two-eq pf₃ pf₄)) = one-eq (R+-cong (∙-cong' pf₁ pf₃) (∙-cong' pf₂ pf₄)) -- simplify
|*-cong (two-eq pf₁ pf₂) (quad-eq pfA pfB pfC pfD) = two-eq (⊕-cong (|*-cong pf₁ pfA) (|*-cong pf₂ pfC)) (⊕-cong (|*-cong pf₁ pfB) (|*-cong pf₂ pfD))

*|-cong : ∀ {s₁ s₂} {x y : Mat s₁ s₂}{u v : Vec s₂} → x m≈ y → u v≈ v → x *| u v≈ y *| v
*|-cong (Sing-eq pf₁) (one-eq pf₂) = one-eq (R*-cong pf₁ pf₂)
*|-cong (RVec-eq pf₁) pf₂ = one-eq (∙-cong' pf₁ pf₂)
*|-cong (CVec-eq pf₁) (one-eq pf₂) = |⊛-cong pf₁ pf₂
*|-cong (quad-eq pfA pfB pfC pfD) (two-eq pf₁ pf₂) = two-eq (⊕-cong (*|-cong pfA pf₁) (*|-cong pfB pf₂)) (⊕-cong (*|-cong pfC pf₁) (*|-cong pfD pf₂))

*-cong : ∀ {s₁ s₂ s₃} {x y : Mat s₁ s₂}{u v : Mat s₂ s₃} → x m≈ y → u m≈ v → x * u m≈ y * v
*-cong (Sing-eq pf₁) (Sing-eq pf₂) = Sing-eq (R*-cong pf₁ pf₂)
*-cong (Sing-eq pf₁) (RVec-eq pf₂) = RVec-eq (⊛|-cong pf₁ pf₂)
*-cong (RVec-eq pf₁) (CVec-eq pf₂) = Sing-eq (∙-cong' pf₁ pf₂)
*-cong (RVec-eq (two-eq pf₁ pf₂)) (quad-eq pfA pfB pfC pfD) = RVec-eq (two-eq (⊕-cong (|*-cong pf₁ pfA) (|*-cong pf₂ pfC)) (⊕-cong (|*-cong pf₁ pfB) (|*-cong pf₂ pfD)))
*-cong (CVec-eq pf₁) (Sing-eq pf₂) = CVec-eq (|⊛-cong pf₁ pf₂)
*-cong (CVec-eq (two-eq pf₁ pf₂)) (RVec-eq (two-eq pf₁' pf₂')) = quad-eq (⊛-cong pf₁ pf₁') (⊛-cong pf₁ pf₂') (⊛-cong pf₂ pf₁') (⊛-cong pf₂ pf₂')
*-cong (quad-eq pfA pfB pfC pfD) (CVec-eq (two-eq pf₁ pf₂)) = CVec-eq (two-eq (⊕-cong (*|-cong pfA pf₁) (*|-cong pfB pf₂)) (⊕-cong (*|-cong pfC pf₁) (*|-cong pfD pf₂)))
*-cong (quad-eq pfA pfB pfC pfD) (quad-eq pfA' pfB' pfC' pfD') = quad-eq (+-cong (*-cong pfA pfA') (*-cong pfB pfC')) (+-cong (*-cong pfA pfB') (*-cong pfB pfD')) (+-cong (*-cong pfC pfA') (*-cong pfD pfC')) (+-cong (*-cong pfC pfB') (*-cong pfD pfD'))