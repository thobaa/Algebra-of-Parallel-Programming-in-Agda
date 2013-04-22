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


private 
  infix 4 _v≈_ 
  data _v≈_ : ∀ {s'} → Vec s' → Vec s' → Set (l₁ ⊔ l₂) where
    one-eq : ∀ {x y} → (x ≈ y) → one x v≈ one y
    two-eq : ∀ {s₁ s₂} {u₁ v₁ : Vec s₁} {u₂ v₂ : Vec s₂} → 
             (u₁ v≈ v₁) → (u₂ v≈ v₂) → two u₁ u₂ v≈ two v₁ v₂
  
  infix 4 _m≈_
  data _m≈_ : ∀ {s₁ s₂} → Mat s₁ s₂ → Mat s₁ s₂ → Set (l₁ ⊔ l₂) where
    Sing-eq : ∀ {x y} → (x ≈ y) → Sing x m≈ Sing y
    RVec-eq : ∀ {s₁ s₂} {u v : Vec (deeper s₁ s₂)} → (u v≈ v) → RVec u m≈ RVec v 
    CVec-eq : ∀ {s₁ s₂} {u v : Vec (deeper s₁ s₂)} → (u v≈ v) → CVec u m≈ CVec v
    quad-eq : ∀ {r₁ r₂ c₁ c₂} {A₁ A₂ : Mat r₁ c₁} {B₁ B₂ : Mat r₁ c₂} → 
                              {C₁ C₂ : Mat r₂ c₁} {D₁ D₂ : Mat r₂ c₂} → 
                    (A₁ m≈ A₂) → (B₁ m≈ B₂) → (C₁ m≈ C₂) → (D₁ m≈ D₂) → quad A₁ B₁ C₁ D₁ m≈ quad A₂ B₂ C₂ D₂
  



  reflV : ∀ {s₁} → {x : Vec s₁} → x v≈ x
  reflV {one} {one x} = one-eq ≈refl
  reflV {(deeper s₁ s₂)} {two y y'} = two-eq reflV reflV
  reflM : ∀ {s₁ s₂} → {x : Mat s₁ s₂} → x m≈ x
  reflM {one} {one} {Sing x} = Sing-eq ≈refl
  reflM {one} {(deeper s₁ s₂)} {RVec y} = RVec-eq reflV
  reflM {(deeper s₁ s₂)} {one} {CVec y} = CVec-eq reflV
  reflM {(deeper r₁ r₂)} {(deeper c₁ c₂)} {quad A B C D} = quad-eq reflM reflM reflM reflM

  symV : ∀ {s} → {i j : Vec s} → i v≈ j → j v≈ i
  symV (one-eq pf) = one-eq (≈sym pf)
  symV (two-eq pf₁ pf₂) = two-eq (symV pf₁) (symV pf₂)
  symM : ∀ {s₁ s₂} → {i j : Mat s₁ s₂} → i m≈ j → j m≈ i
  symM (Sing-eq pf) = Sing-eq (≈sym pf)
  symM (CVec-eq pf) = CVec-eq (symV pf)
  symM (RVec-eq pf) = RVec-eq (symV pf)
  symM (quad-eq pf₁ pf₂ pf₃ pf₄) = quad-eq (symM pf₁) (symM pf₂) (symM pf₃) (symM pf₄)

  
  transV : ∀ {s} → {i j k : Vec s} → i v≈ j → j v≈ k → i v≈ k
  transV (one-eq pf₁) (one-eq pf₂) = one-eq (≈trans pf₁ pf₂)
  transV (two-eq pf₁ pf₂) (two-eq pf₃ pf₄) = two-eq (transV pf₁ pf₃) (transV pf₂ pf₄)
  transM : ∀ {s₁ s₂} → {i j k : Mat s₁ s₂} → i m≈ j → j m≈ k → i m≈ k
  transM (Sing-eq pf₁) (Sing-eq pf₂) = Sing-eq (≈trans pf₁ pf₂)
  transM (RVec-eq pf₁) (RVec-eq pf₂) = RVec-eq (transV pf₁ pf₂)
  transM (CVec-eq pf₁) (CVec-eq pf₂) = CVec-eq (transV pf₁ pf₂)
  transM (quad-eq pf₁ pf₂ pf₃ pf₄) (quad-eq pf₁' pf₂' pf₃' pf₄') = quad-eq (transM pf₁ pf₁') (transM pf₂ pf₂') (transM pf₃ pf₃') (transM pf₄ pf₄')

  
  isEquivalenceV : ∀ {s} → IsEquivalence (_v≈_ {s})
  isEquivalenceV = record
    { refl  = reflV
    ; sym   = symV
    ; trans = transV
    }


  isEquivalenceM : ∀ {s₁ s₂ : Splitting} → IsEquivalence (_m≈_ {s₁} {s₂})
  isEquivalenceM = record 
    { refl = reflM
    ; sym = symM
    ; trans = transM }

  -- not to be here
  setoidM : ∀ {s₁ s₂} → Setoid l₁ (l₂ ⊔ l₁)
  setoidM {s₁} {s₂} = record { Carrier = Mat s₁ s₂; _≈_ = _m≈_; isEquivalence = isEquivalenceM }

  
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
    { isEquivalence = isEquivalenceM
    ; assoc = assocM
    ; ∙-cong = +-cong }

  isSemigroupV : ∀ {s} → IsSemigroup _v≈_ (_⊕_ {s})
  isSemigroupV = record 
    { isEquivalence = isEquivalenceV
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