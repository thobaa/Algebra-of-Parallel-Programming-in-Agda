open import Valiant.Abstract.NonAssociativeNonRing
open import Valiant.Abstract.NonAssociativeNonRing.Structure
open import Algebra
open import Algebra.Structures
import Algebra.FunctionProperties
open import Relation.Binary.PropositionalEquality as PE
  using ()--_≡_; refl; sym; cong; cong₂)

open import Relation.Binary using (Rel; IsEquivalence; Setoid)
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

open import Level


open NonAssociativeNonRing NAR using (_≈_) renaming (refl to ≈refl; sym to ≈sym; trans to ≈trans; +-assoc to R+-assoc; +-comm to R+-comm; +-identity to R+-identity; +-cong to R+-cong; *-cong to R*-cong; distrib to R-distrib; +-commutativeMonoid to R-commutativeMonoid)


-- equality, only equal if have same splitting.
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


infix 4 _≋_
data _≋_ : ∀ {s'} → Tri s' → Tri s' → Set (l₁ ⊔ l₂) where
  one-eq : one ≋ one
  two-eq : ∀ {s₁ s₂} {U₁ U₂ : Tri s₁} {R₁ R₂ : Mat s₁ s₂} {L₁ L₂ : Tri s₂} → 
           U₁ ≋ U₂ → R₁ m≈ R₂ → L₁ ≋ L₂ → two U₁ R₁ L₁ ≋ two U₂ R₂ L₂

private
  reflV : ∀ {s₁} → {x : Vec s₁} → x v≈ x
  reflV {one} {one x} = one-eq ≈refl
  reflV {(deeper s₁ s₂)} {two y y'} = two-eq reflV reflV
  reflM : ∀ {s₁ s₂} → {x : Mat s₁ s₂} → x m≈ x
  reflM {one} {one} {Sing x} = Sing-eq ≈refl
  reflM {one} {(deeper s₁ s₂)} {RVec y} = RVec-eq reflV
  reflM {(deeper s₁ s₂)} {one} {CVec y} = CVec-eq reflV
  reflM {(deeper r₁ r₂)} {(deeper c₁ c₂)} {quad A B C D} = quad-eq reflM reflM reflM reflM
  refl' : ∀ {s} → {x : Tri s} → x ≋ x
  refl' {one}          {one} = one-eq
  refl' {deeper s₁ s₂} {two U R L} = two-eq refl' reflM refl'

  symV : ∀ {s} → {i j : Vec s} → i v≈ j → j v≈ i
  symV (one-eq pf) = one-eq (≈sym pf)
  symV (two-eq pf₁ pf₂) = two-eq (symV pf₁) (symV pf₂)
  symM : ∀ {s₁ s₂} → {i j : Mat s₁ s₂} → i m≈ j → j m≈ i
  symM (Sing-eq pf) = Sing-eq (≈sym pf)
  symM (CVec-eq pf) = CVec-eq (symV pf)
  symM (RVec-eq pf) = RVec-eq (symV pf)
  symM (quad-eq pf₁ pf₂ pf₃ pf₄) = quad-eq (symM pf₁) (symM pf₂) (symM pf₃) (symM pf₄)
  sym' : ∀ {s} → {i j : Tri s} → i ≋ j → j ≋ i
  sym' one-eq = one-eq
  sym' (two-eq pfU pfR pfL) = two-eq (sym' pfU) (symM pfR) (sym' pfL)
  --sym' --{deeper s₁ s₂} (two-eq pfU pfR pfL) = two-eq (sym' pfU) (symM pfR) (sym' pfL)

  transV : ∀ {s} → {i j k : Vec s} → i v≈ j → j v≈ k → i v≈ k
  transV (one-eq pf₁) (one-eq pf₂) = one-eq (≈trans pf₁ pf₂)
  transV (two-eq pf₁ pf₂) (two-eq pf₃ pf₄) = two-eq (transV pf₁ pf₃) (transV pf₂ pf₄)
  transM : ∀ {s₁ s₂} → {i j k : Mat s₁ s₂} → i m≈ j → j m≈ k → i m≈ k
  transM (Sing-eq pf₁) (Sing-eq pf₂) = Sing-eq (≈trans pf₁ pf₂)
  transM (RVec-eq pf₁) (RVec-eq pf₂) = RVec-eq (transV pf₁ pf₂)
  transM (CVec-eq pf₁) (CVec-eq pf₂) = CVec-eq (transV pf₁ pf₂)
  transM (quad-eq pf₁ pf₂ pf₃ pf₄) (quad-eq pf₁' pf₂' pf₃' pf₄') = quad-eq (transM pf₁ pf₁') (transM pf₂ pf₂') (transM pf₃ pf₃') (transM pf₄ pf₄')
  trans' : ∀ {s} → {i j k : Tri s} → i ≋ j → j ≋ k → i ≋ k
  trans' one-eq one-eq = one-eq
  trans' (two-eq pfU pfR pfL) (two-eq pfU' pfR' pfL') = two-eq (trans' pfU pfU') (transM pfR pfR') (trans' pfL pfL')
isEquivalence : ∀ {s} → IsEquivalence (_≋_ {s})
isEquivalence = record
  { refl  = refl'
  ; sym   = sym'
  ; trans = trans'
  }

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
  }

setoidM : ∀ {s₁ s₂} → Setoid l₁ (l₂ ⊔ l₁)
setoidM {s₁} {s₂} = record { Carrier = Mat s₁ s₂; _≈_ = _m≈_; isEquivalence = isEquivalenceM }

--open Algebra.FunctionProperties (_≋_  {s})

private 
  -- helper functions: 
  assocV : {s : Splitting} → (x y z : Vec s) → (x ⊕ y) ⊕ z v≈ x ⊕ (y ⊕ z)
  assocV (one x) (one y) (one z) = one-eq (R+-assoc x y z)
  assocV (two u₁ v₁) (two u₂ v₂) (two u₃ v₃) = two-eq (assocV u₁ u₂ u₃) (assocV v₁ v₂ v₃)

  assocM : {s₁ s₂ : Splitting} → (x y z : Mat s₁ s₂) → (x + y) + z m≈ x + (y + z)
  assocM (Sing x) (Sing y) (Sing z) = Sing-eq (R+-assoc x y z)
  assocM (RVec x) (RVec y) (RVec z) = RVec-eq (assocV x y z)
  assocM (CVec x) (CVec y) (CVec z) = CVec-eq (assocV x y z)
  assocM (quad A₁ B₁ C₁ D₁) (quad A₂ B₂ C₂ D₂) (quad A₃ B₃ C₃ D₃) = quad-eq (assocM A₁ A₂ A₃) (assocM B₁ B₂ B₃) (assocM C₁ C₂ C₃) (assocM D₁ D₂ D₃)

  assoc' : {s₀ : Splitting} → (x y z : Tri s₀) → (x ◂+ y) ◂+ z ≋ x ◂+ (y ◂+ z)
  assoc' one one one = one-eq
  assoc' (two U₁ R₁ L₁) (two U₂ R₂ L₂) (two U₃ R₃ L₃) = two-eq (assoc' U₁ U₂ U₃) (assocM R₁ R₂ R₃) (assoc' L₁ L₂ L₃)

  commV : ∀ {s} → (x y : Vec s) → x ⊕ y v≈ y ⊕ x
  commV (one x) (one y) = one-eq (R+-comm x y)
  commV (two u₁ v₁) (two u₂ v₂) = two-eq (commV u₁ u₂) (commV v₁ v₂)
  commM : ∀ {s₁ s₂} → (x y : Mat s₁ s₂) → x + y m≈ y + x
  commM (Sing x) (Sing y) = Sing-eq (R+-comm x y)
  commM (RVec u) (RVec v) = RVec-eq (commV u v)
  commM (CVec u) (CVec v) = CVec-eq (commV u v)
  commM (quad A₁ B₁ C₁ D₁) (quad A₂ B₂ C₂ D₂) = quad-eq (commM A₁ A₂) (commM B₁ B₂) (commM C₁ C₂) (commM D₁ D₂)

  comm' : ∀ {s} → (x y : Tri s) → x ◂+ y ≋ y ◂+ x
  comm' one one = one-eq
  comm' (two U₁ R₁ L₁) (two U₂ R₂ L₂) = two-eq (comm' U₁ U₂) (commM R₁ R₂) (comm' L₁ L₂)
  
  identityˡV : ∀ {s} → (x : Vec s) → zeroVec ⊕ x v≈ x 
  identityˡV (one x) = one-eq (proj₁ R+-identity x)
  identityˡV (two u v) = two-eq (identityˡV u) (identityˡV v)
  identityˡM : ∀ {s₁ s₂} → (x : Mat s₁ s₂) → zeroMat + x m≈ x 
  identityˡM (Sing x) = Sing-eq (proj₁ R+-identity x)
  identityˡM (RVec u) = RVec-eq (identityˡV u)
  identityˡM (CVec u) = CVec-eq (identityˡV u)
  identityˡM (quad A B C D) = quad-eq (identityˡM A) (identityˡM B) (identityˡM C) (identityˡM D)

  identityˡT : ∀ {s} → (x : Tri s) → zeroTri ◂+ x ≋ x 
  identityˡT one = one-eq
  identityˡT (two U R L) = two-eq (identityˡT U) (identityˡM R) (identityˡT L)
  
  ⊕-cong : ∀ {s} {x y u v : Vec s} → x v≈ y → u v≈ v → x ⊕ u v≈ y ⊕ v
  ⊕-cong (one-eq pf₁) (one-eq pf₂) = one-eq (R+-cong pf₁ pf₂)
  ⊕-cong (two-eq pf₁ pf₂) (two-eq pf₃ pf₄) = two-eq (⊕-cong pf₁ pf₃) (⊕-cong pf₂ pf₄)
  
  +-cong : ∀ {s₁ s₂} {x y u v : Mat s₁ s₂} → x m≈ y → u m≈ v → x + u m≈ y + v
  +-cong (Sing-eq pf₁) (Sing-eq pf₂) = Sing-eq (R+-cong pf₁ pf₂)
  +-cong (RVec-eq pf₁) (RVec-eq pf₂) = RVec-eq (⊕-cong pf₁ pf₂)
  +-cong (CVec-eq pf₁) (CVec-eq pf₂) = CVec-eq (⊕-cong pf₁ pf₂)
  +-cong (quad-eq pf₁ pf₂ pf₃ pf₄) (quad-eq pf₁' pf₂' pf₃' pf₄') = quad-eq (+-cong pf₁ pf₁') (+-cong pf₂ pf₂') (+-cong pf₃ pf₃') (+-cong pf₄ pf₄')

  ◂+-cong : ∀ {s} {x y u v : Tri s} → x ≋ y → u ≋ v → x ◂+ u ≋ y ◂+ v
  ◂+-cong one-eq one-eq = one-eq
  ◂+-cong (two-eq pfU₁ pfR₁ pfL₁) (two-eq pfU₂ pfR₂ pfL₂) = two-eq (◂+-cong pfU₁ pfU₂) (+-cong pfR₁ pfR₂) (◂+-cong pfL₁ pfL₂)
isSemigroup : ∀ {s} → IsSemigroup _≋_ (_◂+_ {s})
isSemigroup = record 
  { isEquivalence = isEquivalence
  ; assoc         = assoc'
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

isCommutativeMonoid : ∀ {s} → IsCommutativeMonoid _≋_ (_◂+_ {s}) zeroTri
isCommutativeMonoid = record 
  { isSemigroup = isSemigroup
  ; identityˡ   = identityˡT
  ; comm        = comm'
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
  ; _≈_                 = _≋_
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



-- left to do: also, clean things up by giving proper names "Associative" etc 
-- think about ∀ s, should probably not parametrize by it.
private 
  ⊛|-cong : ∀ {s} {x y : R} {u v : Vec s} → x ≈ y → u v≈ v → x ⊛| u v≈ y ⊛| v
  ⊛|-cong pf₁ (one-eq pf₂) = one-eq (R*-cong pf₁ pf₂)
  ⊛|-cong pf₁ (two-eq pf₂ pf₃) = two-eq (⊛|-cong pf₁ pf₂) (⊛|-cong pf₁ pf₃)

  |⊛-cong : ∀ {s} {x y : Vec s}{u v : R}  → x v≈ y → u ≈ v → x |⊛ u v≈ y |⊛ v
  |⊛-cong (one-eq pf₁) pf₂ = one-eq (R*-cong pf₁ pf₂)
  |⊛-cong (two-eq pf₁ pf₂) pf₃ = two-eq (|⊛-cong pf₁ pf₃) (|⊛-cong pf₂ pf₃)

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

  ◂|-cong : ∀ {s} {x y : Tri s}{u v : Vec s} → x ≋ y → u v≈ v → x ◂| u v≈ y ◂| v
  ◂|-cong one-eq pf = one-eq ≈refl
  ◂|-cong (two-eq pfU pfR pfL) (two-eq pf₁ pf₂) = two-eq (⊕-cong (◂|-cong pfU pf₁) (*|-cong pfR pf₂)) (◂|-cong pfL pf₂)

  |◂-cong : ∀ {s} {x y : Vec s}{u v : Tri s} → x v≈ y → u ≋ v → x |◂ u v≈ y |◂ v
  |◂-cong pf one-eq = one-eq ≈refl
  |◂-cong (two-eq pf₁ pf₂) (two-eq pfU pfR pfL) = two-eq (|◂-cong pf₁ pfU) (⊕-cong (|*-cong pf₁ pfR) (|◂-cong pf₂ pfL))

  ◂*-cong : ∀ {s₁ s₂} {x y : Tri s₁}{u v : Mat s₁ s₂} → x ≋ y → u m≈ v → x ◂* u m≈ y ◂* v
  ◂*-cong one-eq (Sing-eq y') = Sing-eq ≈refl
  ◂*-cong one-eq (RVec-eq y) = RVec-eq reflV
  ◂*-cong pf₁ (CVec-eq pf₂) = CVec-eq (◂|-cong pf₁ pf₂)
  ◂*-cong (two-eq pfU pfR pfL) (quad-eq pfA pfB pfC pfD) = quad-eq (+-cong (◂*-cong pfU pfA) (*-cong pfR pfC)) (+-cong (◂*-cong pfU pfB) (*-cong pfR pfD)) (◂*-cong pfL pfC) (◂*-cong pfL pfD)

  *◂-cong : ∀ {s₁ s₂} {x y : Mat s₁ s₂}{u v : Tri s₂} → x m≈ y → u ≋ v → x *◂ u m≈ y *◂ v
  *◂-cong (Sing-eq pf) one-eq = Sing-eq ≈refl
  *◂-cong (RVec-eq pf₁) pf₂ = RVec-eq (|◂-cong pf₁ pf₂)
  *◂-cong (CVec-eq pf) one-eq = CVec-eq reflV
  *◂-cong (quad-eq pfA pfB pfC pfD) (two-eq pfU pfR pfL) = quad-eq (*◂-cong pfA pfU) (+-cong (*-cong pfA pfR) (*◂-cong pfB pfL)) (*◂-cong pfC pfU) (+-cong (*-cong pfC pfR) (*◂-cong pfD pfL))
  ◂-cong : ∀ {s} → {x y u v : Tri s} → x ≋ y → u ≋ v → x ◂ u ≋ y ◂ v
  ◂-cong one-eq one-eq = one-eq
  ◂-cong (two-eq pfU₁ pfR₁ pfL₁) (two-eq pfU₂ pfR₂ pfL₂) = two-eq (◂-cong pfU₁ pfU₂) (+-cong (◂*-cong pfU₁ pfR₂) (*◂-cong pfR₁ pfL₂)) (◂-cong pfL₁ pfL₂)


  -- this should be moved to helper definitions.
  rearrangeLemma : ∀ {a b}{cm : CommutativeMonoid a b} (x y z å : CommutativeMonoid.Carrier cm) → (CommutativeMonoid._≈_ cm)
                                                                                                  ((CommutativeMonoid._∙_ cm) ((CommutativeMonoid._∙_ cm) x y) ((CommutativeMonoid._∙_ cm) z å)) 
                                                                                                  ((CommutativeMonoid._∙_ cm) ((CommutativeMonoid._∙_ cm) x z) ((CommutativeMonoid._∙_ cm) y å)) 
  rearrangeLemma {cm = cm} x y z å = begin 
                 (x +' y) +' (z +' å) 
                   ≈⟨ sym (assoc (x +' y) z å) ⟩ 
                 ((x +' y) +' z) +' å 
                   ≈⟨ ∙-cong (assoc x y z) refl ⟩   
                 (x +' (y +' z)) +' å 
                   ≈⟨ ∙-cong (∙-cong refl (comm y z)) refl ⟩   
                 (x +' (z +' y)) +' å 
                   ≈⟨ ∙-cong (sym (assoc x z y)) refl ⟩   
                 ((x +' z) +' y) +' å 
                   ≈⟨ assoc (x +' z) y å ⟩ 
                 (x +' z) +' (y +' å) ∎
    where open EqR (CommutativeMonoid.setoid cm)
          open CommutativeMonoid cm renaming (_∙_ to _+'_)

  rearrangeLemma' : ∀ {a b}{cm : CommutativeMonoid a b} (x y a b c d : CommutativeMonoid.Carrier cm) → (CommutativeMonoid._≈_ cm) x (CommutativeMonoid._∙_ cm a b) → 
                                                                                                       (CommutativeMonoid._≈_ cm) y (CommutativeMonoid._∙_ cm c d) → 
                                                                                                  (CommutativeMonoid._≈_ cm) ((CommutativeMonoid._∙_ cm) x y) 
                                                                                                  ((CommutativeMonoid._∙_ cm) ((CommutativeMonoid._∙_ cm) a c) ((CommutativeMonoid._∙_ cm) b d)) 
  rearrangeLemma' {cm = cm} x y a b c d x≈a∙b y≈c∙d = begin 
                  x +' y 
                    ≈⟨ ∙-cong x≈a∙b y≈c∙d ⟩ 
                  a +' b +' (c +' d)
                    ≈⟨ rearrangeLemma {cm = cm} a b c d ⟩ 
                  (a +' c) +' (b +' d) ∎
    where open EqR (CommutativeMonoid.setoid cm)
          open CommutativeMonoid cm renaming (_∙_ to _+'_)

  ∙-distribˡ : ∀ {s} → (u v w : Vec s) → u ∙ (v ⊕ w) ≈ u ∙ v R+ u ∙ w
  ∙-distribˡ (Valiant.Concrete.Mat.one x) (Valiant.Concrete.Mat.one y) (Valiant.Concrete.Mat.one z) = proj₁ R-distrib x y z
  ∙-distribˡ (Valiant.Concrete.Mat.two u₁ v₁) (Valiant.Concrete.Mat.two u₂ v₂) (Valiant.Concrete.Mat.two u₃ v₃) = rearrangeLemma' {cm = R-commutativeMonoid} (u₁ ∙ (u₂ ⊕ u₃)) (v₁ ∙ (v₂ ⊕ v₃)) (u₁ ∙ u₂) (u₁ ∙ u₃) (v₁ ∙ v₂) (v₁ ∙ v₃) (∙-distribˡ u₁ u₂ u₃) (∙-distribˡ v₁ v₂ v₃)

  |⊛-distribˡ : ∀ {s} → (u : Vec s) (x y : R) → u |⊛ (x R+ y) v≈ u |⊛ x ⊕ u |⊛ y
  |⊛-distribˡ (Valiant.Concrete.Mat.one x) y z = one-eq (proj₁ R-distrib x y z)
  |⊛-distribˡ (Valiant.Concrete.Mat.two u v) x y = two-eq (|⊛-distribˡ u x y) (|⊛-distribˡ v x y)
    
  *|-distribˡ : ∀ {s₁ s₂} → (x : Mat s₁ s₂) (u v : Vec s₂) → x *| (u ⊕ v) v≈ x *| u ⊕ x *| v
  *|-distribˡ (Sing x) (Valiant.Concrete.Mat.one y) (Valiant.Concrete.Mat.one z) = one-eq (proj₁ R-distrib x y z)
  *|-distribˡ (Valiant.Concrete.Mat.RVec u) v w = one-eq (∙-distribˡ u v w)
  *|-distribˡ (Valiant.Concrete.Mat.CVec u) (Valiant.Concrete.Mat.one x) (Valiant.Concrete.Mat.one y) = |⊛-distribˡ u x y
  *|-distribˡ (Valiant.Concrete.Mat.quad A B C D) (Valiant.Concrete.Mat.two u v) (Valiant.Concrete.Mat.two u' v') = two-eq 
    (rearrangeLemma' {cm = commutativeMonoidV} (A *| (u ⊕ u')) (B *| (v ⊕ v')) (A *| u) (A *| u') (B *| v) (B *| v') (*|-distribˡ A u u') (*|-distribˡ B v v')) 
    (rearrangeLemma' {cm = commutativeMonoidV} (C *| (u ⊕ u')) (D *| (v ⊕ v')) (C *| u) (C *| u') (D *| v) (D *| v') (*|-distribˡ C u u') (*|-distribˡ D v v')) 

  *-distribˡ : ∀ {s₁ s₂ s₃} → (x : Mat s₁ s₂) (y z : Mat s₂ s₃) → x * (y + z) m≈ x * y + x * z
  *-distribˡ (Sing x) (Sing y) (Sing z) = Sing-eq (proj₁ R-distrib x y z)
  *-distribˡ (Sing x) (RVec u) (RVec v) = {!!}
  *-distribˡ (RVec v) (CVec v') (CVec v0) = {!!}
  *-distribˡ (RVec v) (quad A B C D) (quad A' B' C' D') = {!!}
  *-distribˡ (CVec v) (Sing x) (Sing x') = {!!}
  *-distribˡ (CVec v) (RVec v') (RVec v0) = {!!}
  *-distribˡ (quad A B C D) (CVec v) (CVec v') = {!!}
  *-distribˡ (quad A B C D) (quad A' B' C' D') (quad A0 B0 C0 D0) = {!!}

  ◂|-distribˡ : ∀ {s} → (x : Tri s) (u v : Vec s) → x ◂| (u ⊕ v) v≈ x ◂| u ⊕ x ◂| v
  ◂|-distribˡ one (one x) (one x') = one-eq (≈sym (proj₁ R+-identity R0)) --symV (proj₁ {!R+-identity!})
  ◂|-distribˡ (two U R L) (two u₁ v₁) (two u₂ v₂) = two-eq (rearrangeLemma' {cm = commutativeMonoidV} (U ◂| (u₁ ⊕ u₂)) (R *| (v₁ ⊕ v₂)) (U ◂| u₁) (U ◂| u₂) (R *| v₁) (R *| v₂) (◂|-distribˡ U u₁ u₂) (*|-distribˡ R v₁ v₂)) (◂|-distribˡ L v₁ v₂)
  ◂|-distribʳ : ∀ {s} → (x y : Tri s) (v : Vec s) → (x ◂+ y) ◂| v v≈ x ◂| v ⊕ y ◂| v
  ◂|-distribʳ x u v = {!!}
  ◂*-distribˡ : ∀ {s₁ s₂} → (x : Tri s₁) (y z : Mat s₁ s₂) → x ◂* (y + z) m≈ (x ◂* y + x ◂* z)
  ◂*-distribˡ one (Sing _) (Sing _) = Sing-eq (≈sym (proj₁ R+-identity R0))
  ◂*-distribˡ one (RVec _) (RVec _) = RVec-eq (two-eq (symV (identityˡV zeroVec)) (symV (identityˡV zeroVec)))
  ◂*-distribˡ (two U R L) (CVec u) (CVec v) = CVec-eq (◂|-distribˡ (two U R L) u v)
  ◂*-distribˡ (two U R L) (quad A B C D) (quad A' B' C' D') = quad-eq (rearrangeLemma' {cm = commutativeMonoidM} (U ◂* (A + A')) (R * (C + C')) (U ◂* A) (U ◂* A') (R * C) (R * C') (◂*-distribˡ U A A') (*-distribˡ R C C')) (rearrangeLemma' {cm = commutativeMonoidM} (U ◂* (B + B')) (R * (D + D')) (U ◂* B) (U ◂* B') (R * D) (R * D') (◂*-distribˡ U B B') {!!}) (◂*-distribˡ L C C') (◂*-distribˡ L D D')

  ◂*-distribʳ : ∀ {s₁ s₂} → (x y : Tri s₁) (z : Mat s₁ s₂) → (x ◂+ y) ◂* z m≈ x ◂* z + y ◂* z
  ◂*-distribʳ one one (Sing x) = Sing-eq (≈sym (proj₁ R+-identity R0))
  ◂*-distribʳ one one (RVec y) = RVec-eq (two-eq (symV (identityˡV zeroVec)) (symV (identityˡV zeroVec)))
  ◂*-distribʳ (two U R L) (two U' R' L') (CVec (two u v)) = CVec-eq {!!}
  ◂*-distribʳ (two U R L) (two U' R' L') (quad A B C D) = quad-eq {!!} {!!} (◂*-distribʳ L L' C) (◂*-distribʳ L L' D)

  *◂-distribˡ : ∀ {s₁ s₂} → (x : Mat s₁ s₂) (y z : Tri s₂) → x *◂ (y ◂+ z) m≈ (x *◂ y + x *◂ z)
  *◂-distribˡ x y z = {!!} 

  *◂-distribʳ : ∀ {s₁ s₂} → (x y : Mat s₁ s₂) (z : Tri s₂) → (x + y) *◂ z m≈ x *◂ z + y *◂ z
  *◂-distribʳ x y z = {!!}
  

  distribˡ : ∀ {s} → (x y z : Tri s) → x ◂ (y ◂+ z) ≋ x ◂ y ◂+ x ◂ z -- (U₁ ◂* R₂ + U₁ ◂* R₃) + (R₁ *◂ L₂ + R₁ *◂ L₃) m≈
  distribˡ one one one = one-eq
  distribˡ (two U₁ R₁ L₁) (two U₂ R₂ L₂) (two U₃ R₃ L₃) = two-eq (distribˡ U₁ U₂ U₃) (transM (+-cong (◂*-distribˡ U₁ R₂ R₃) (*◂-distribˡ R₁ L₂ L₃)) (rearrangeLemma {cm = commutativeMonoidM} (U₁ ◂* R₂) (U₁ ◂* R₃) (R₁ *◂ L₂) (R₁ *◂ L₃))) --(lemma U₁ R₁ R₂ R₃ L₂ L₃) 
                                                                                     (distribˡ L₁ L₂ L₃)

  distribʳ : ∀ {s} → (x y z : Tri s) → (y ◂+ z) ◂ x ≋ y ◂ x ◂+ z ◂ x
  distribʳ one one one = one-eq
  distribʳ (two U₁ R₁ L₁) (two U₂ R₂ L₂) (two U₃ R₃ L₃) = two-eq (distribʳ U₁ U₂ U₃) (begin (U₂ ◂+ U₃) ◂* R₁ + (R₂ + R₃) *◂ L₁ 
                                                                                              ≈⟨ +-cong (◂*-distribʳ U₂ U₃ R₁) (*◂-distribʳ R₂ R₃ L₁) ⟩ 
                                                                                            (U₂ ◂* R₁ + U₃ ◂* R₁) + (R₂ *◂ L₁ + R₃ *◂ L₁)
                                                                                              ≈⟨ rearrangeLemma {cm = commutativeMonoidM} (U₂ ◂* R₁) (U₃ ◂* R₁) (R₂ *◂ L₁) (R₃ *◂ L₁) ⟩
                                                                                            (U₂ ◂* R₁ + R₂ *◂ L₁) + (U₃ ◂* R₁ + R₃ *◂ L₁) ∎)
                                                                 (distribʳ L₁ L₂ L₃)
    where open EqR setoidM

  distrib : ∀ {s} → Σ ((x y z : Tri s) → x ◂ (y ◂+ z) ≋ x ◂ y ◂+ x ◂ z) (λ x → (x' y z : Tri s) → (y ◂+ z) ◂ x' ≋ y ◂ x' ◂+ z ◂ x')
  distrib = distribˡ , distribʳ


  -- zero stuff
  sumLemma : ∀ {a b} {cm : CommutativeMonoid a b} {x y : CommutativeMonoid.Carrier cm} → (CommutativeMonoid._≈_ cm) x (CommutativeMonoid.ε cm) → 
                                                                                         (CommutativeMonoid._≈_ cm) y (CommutativeMonoid.ε cm) → 
                                                                                         (CommutativeMonoid._≈_ cm) ((CommutativeMonoid._∙_ cm) x y) (CommutativeMonoid.ε cm)
  sumLemma {cm = cm} {x} {y} x≈ε y≈ε = begin 
           x +' y 
             ≈⟨ ∙-cong x≈ε y≈ε ⟩
           ε +' ε
             ≈⟨ identityˡ ε ⟩
           ε ∎
    where open CommutativeMonoid cm renaming (_∙_ to _+'_)
          open EqR setoid

  

  ◂*-zeroˡ : {s₁ s₂ : _} → (x : Mat s₁ s₂) → zeroTri ◂* x m≈ zeroMat
  ◂*-zeroˡ (Sing x) = Sing-eq ≈refl
  ◂*-zeroˡ (RVec v) = reflM
  ◂*-zeroˡ (CVec (two y y')) = CVec-eq (two-eq {!!} {!!})
  ◂*-zeroˡ (quad A B C D) = quad-eq {!!} {!!} {!!} {!!}

  *◂-zeroˡ : {s₁ s₂ : _} → (x : Tri s₂) → zeroMat {s₁} {s₂}*◂ x m≈ zeroMat
  *◂-zeroˡ x = {!!}

  ◂*-zeroʳ : {s₁ s₂ : _} → (x : Tri s₁) → x ◂* zeroMat {s₁} {s₂} m≈ zeroMat
  ◂*-zeroʳ x = {!!}

  *◂-zeroʳ : {s₁ s₂ : _} → (x : Mat s₁ s₂) → x *◂ zeroTri m≈ zeroMat
  *◂-zeroʳ x = {!!}

  zeroˡ : {s : _} → (x : Tri s) → zeroTri ◂ x ≋ zeroTri
  zeroˡ one = one-eq
  zeroˡ (two U R L) = two-eq (zeroˡ U) (sumLemma {cm = commutativeMonoidM} (◂*-zeroˡ R) (*◂-zeroˡ L))
                                                  (zeroˡ L)
  zeroʳ : {s : _} → (x : Tri s) → x ◂ zeroTri ≋ zeroTri
  zeroʳ one = one-eq
  zeroʳ (two U R L) = two-eq (zeroʳ U) (sumLemma {cm = commutativeMonoidM} (◂*-zeroʳ U) (*◂-zeroʳ R))
                                                  (zeroʳ L)

  zeroTri-zero : ∀ {s} → Σ ((x : Tri s) → zeroTri ◂ x ≋ zeroTri) (λ x → (x' : Tri s) → x' ◂ zeroTri ≋ zeroTri)
  zeroTri-zero = zeroˡ , zeroʳ

isNonAssociativeNonRing : ∀ {s} → IsNonAssociativeNonRing _≋_ (_◂+_ {s}) (_◂_ {s}) zeroTri
isNonAssociativeNonRing = record 
  { +-isCommutativeMonoid = isCommutativeMonoid
  ; *-cong = ◂-cong
  ; distrib = distrib
  ; zero = zeroTri-zero
  }

isNonAssociativeNonRingM : ∀ {s} → IsNonAssociativeNonRing _m≈_ (_+_ {s} {s}) (_*_) zeroMat
isNonAssociativeNonRingM = record 
  { +-isCommutativeMonoid = isCommutativeMonoidM
  ; *-cong = *-cong
  ; distrib = {!*-distribˡ , *-distribʳ!}
  ; zero = {!*-zeroˡ!} , {!*-zeroʳ!} 
  }