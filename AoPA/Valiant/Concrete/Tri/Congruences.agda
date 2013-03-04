open import Valiant.Abstract.NonAssociativeNonRing

module Valiant.Concrete.Tri.Congruences {l₁ l₂} (NAR : NonAssociativeNonRing l₁ l₂) where


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
open NonAssociativeNonRing NAR using (_≈_) renaming (refl to ≈refl; sym to ≈sym; trans to ≈trans; +-assoc to R+-assoc; +-comm to R+-comm; +-identity to R+-identity; +-cong to R+-cong; *-cong to R*-cong; distrib to R-distrib; +-commutativeMonoid to R-commutativeMonoid)


⊕-cong : ∀ {s} {x y u v : Vec s} → x v≈ y → u v≈ v → x ⊕ u v≈ y ⊕ v
⊕-cong (one-eq pf₁) (one-eq pf₂) = one-eq (R+-cong pf₁ pf₂)
⊕-cong (two-eq pf₁ pf₂) (two-eq pf₃ pf₄) = two-eq (⊕-cong pf₁ pf₃) (⊕-cong pf₂ pf₄)
  

+-cong : ∀ {s₁ s₂} {x y u v : Mat s₁ s₂} → x m≈ y → u m≈ v → x + u m≈ y + v
+-cong (Sing-eq pf₁) (Sing-eq pf₂) = Sing-eq (R+-cong pf₁ pf₂)
+-cong (RVec-eq pf₁) (RVec-eq pf₂) = RVec-eq (⊕-cong pf₁ pf₂)
+-cong (CVec-eq pf₁) (CVec-eq pf₂) = CVec-eq (⊕-cong pf₁ pf₂)
+-cong (quad-eq pf₁ pf₂ pf₃ pf₄) (quad-eq pf₁' pf₂' pf₃' pf₄') = quad-eq (+-cong pf₁ pf₁') (+-cong pf₂ pf₂') (+-cong pf₃ pf₃') (+-cong pf₄ pf₄')

◂+-cong : ∀ {s} {x y u v : Tri s} → x t≈ y → u t≈ v → x ◂+ u t≈ y ◂+ v
◂+-cong one-eq one-eq = one-eq
◂+-cong (two-eq pfU₁ pfR₁ pfL₁) (two-eq pfU₂ pfR₂ pfL₂) = two-eq (◂+-cong pfU₁ pfU₂) (+-cong pfR₁ pfR₂) (◂+-cong pfL₁ pfL₂)


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

◂|-cong : ∀ {s} {x y : Tri s}{u v : Vec s} → x t≈ y → u v≈ v → x ◂| u v≈ y ◂| v
◂|-cong one-eq pf = one-eq ≈refl
◂|-cong (two-eq pfU pfR pfL) (two-eq pf₁ pf₂) = two-eq (⊕-cong (◂|-cong pfU pf₁) (*|-cong pfR pf₂)) (◂|-cong pfL pf₂)

|◂-cong : ∀ {s} {x y : Vec s}{u v : Tri s} → x v≈ y → u t≈ v → x |◂ u v≈ y |◂ v
|◂-cong pf one-eq = one-eq ≈refl
|◂-cong (two-eq pf₁ pf₂) (two-eq pfU pfR pfL) = two-eq (|◂-cong pf₁ pfU) (⊕-cong (|*-cong pf₁ pfR) (|◂-cong pf₂ pfL))

◂*-cong : ∀ {s₁ s₂} {x y : Tri s₁}{u v : Mat s₁ s₂} → x t≈ y → u m≈ v → x ◂* u m≈ y ◂* v
◂*-cong one-eq (Sing-eq y') = Sing-eq ≈refl
◂*-cong one-eq (RVec-eq y) = RVec-eq reflV
◂*-cong pf₁ (CVec-eq pf₂) = CVec-eq (◂|-cong pf₁ pf₂)
◂*-cong (two-eq pfU pfR pfL) (quad-eq pfA pfB pfC pfD) = quad-eq (+-cong (◂*-cong pfU pfA) (*-cong pfR pfC)) (+-cong (◂*-cong pfU pfB) (*-cong pfR pfD)) (◂*-cong pfL pfC) (◂*-cong pfL pfD)

*◂-cong : ∀ {s₁ s₂} {x y : Mat s₁ s₂}{u v : Tri s₂} → x m≈ y → u t≈ v → x *◂ u m≈ y *◂ v
*◂-cong (Sing-eq pf) one-eq = Sing-eq ≈refl
*◂-cong (RVec-eq pf₁) pf₂ = RVec-eq (|◂-cong pf₁ pf₂)
*◂-cong (CVec-eq pf) one-eq = CVec-eq reflV
*◂-cong (quad-eq pfA pfB pfC pfD) (two-eq pfU pfR pfL) = quad-eq (*◂-cong pfA pfU) (+-cong (*-cong pfA pfR) (*◂-cong pfB pfL)) (*◂-cong pfC pfU) (+-cong (*-cong pfC pfR) (*◂-cong pfD pfL))
◂-cong : ∀ {s} → {x y u v : Tri s} → x t≈ y → u t≈ v → x ◂ u t≈ y ◂ v
◂-cong one-eq one-eq = one-eq
◂-cong (two-eq pfU₁ pfR₁ pfL₁) (two-eq pfU₂ pfR₂ pfL₂) = two-eq (◂-cong pfU₁ pfU₂) (+-cong (◂*-cong pfU₁ pfR₂) (*◂-cong pfR₁ pfL₂)) (◂-cong pfL₁ pfL₂)

