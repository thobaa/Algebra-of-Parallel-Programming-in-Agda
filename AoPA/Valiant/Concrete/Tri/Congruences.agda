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
import Valiant.Concrete.Mat.Properties 
open Valiant.Concrete.Mat.Properties NAR

import Valiant.Concrete.Tri.Equalities 
open Valiant.Concrete.Tri.Equalities NAR
open NonAssociativeNonRing NAR using (_≈_) renaming (refl to ≈refl; sym to ≈sym; trans to ≈trans; +-assoc to R+-assoc; +-comm to R+-comm; +-identity to R+-identity; +-cong to R+-cong; *-cong to R*-cong; distrib to R-distrib; +-commutativeMonoid to R-commutativeMonoid)


◂+-cong : ∀ {s} {x y u v : Tri s} → x t≈ y → u t≈ v → x ◂+ u t≈ y ◂+ v
◂+-cong one-eq one-eq = one-eq
◂+-cong (two-eq pfU₁ pfR₁ pfL₁) (two-eq pfU₂ pfR₂ pfL₂) = two-eq (◂+-cong pfU₁ pfU₂) (+-cong pfR₁ pfR₂) (◂+-cong pfL₁ pfL₂)

◂|-cong : ∀ {s} {x y : Tri s}{u v : Vec s} → x t≈ y → u v≈ v → x ◂| u v≈ y ◂| v
◂|-cong one-eq pf = one-eq ≈refl
◂|-cong (two-eq pfU pfR pfL) (two-eq pf₁ pf₂) = two-eq (⊕-cong (◂|-cong pfU pf₁) (*|-cong pfR pf₂)) (◂|-cong pfL pf₂)

|◂-cong : ∀ {s} {x y : Vec s}{u v : Tri s} → x v≈ y → u t≈ v → x |◂ u v≈ y |◂ v
|◂-cong pf one-eq = one-eq ≈refl
|◂-cong (two-eq pf₁ pf₂) (two-eq pfU pfR pfL) = two-eq (|◂-cong pf₁ pfU) (⊕-cong (|*-cong pf₁ pfR) (|◂-cong pf₂ pfL))

◂*-cong : ∀ {s₁ s₂} {x y : Tri s₁}{u v : Mat s₁ s₂} → x t≈ y → u m≈ v → x ◂* u m≈ y ◂* v
◂*-cong one-eq (Sing-eq y') = Sing-eq ≈refl
◂*-cong one-eq (RVec-eq y) = RVec-eq v-refl
◂*-cong pf₁ (CVec-eq pf₂) = CVec-eq (◂|-cong pf₁ pf₂)
◂*-cong (two-eq pfU pfR pfL) (quad-eq pfA pfB pfC pfD) = quad-eq (+-cong (◂*-cong pfU pfA) (*-cong pfR pfC)) (+-cong (◂*-cong pfU pfB) (*-cong pfR pfD)) (◂*-cong pfL pfC) (◂*-cong pfL pfD)

*◂-cong : ∀ {s₁ s₂} {x y : Mat s₁ s₂}{u v : Tri s₂} → x m≈ y → u t≈ v → x *◂ u m≈ y *◂ v
*◂-cong (Sing-eq pf) one-eq = Sing-eq ≈refl
*◂-cong (RVec-eq pf₁) pf₂ = RVec-eq (|◂-cong pf₁ pf₂)
*◂-cong (CVec-eq pf) one-eq = CVec-eq v-refl
*◂-cong (quad-eq pfA pfB pfC pfD) (two-eq pfU pfR pfL) = quad-eq (*◂-cong pfA pfU) (+-cong (*-cong pfA pfR) (*◂-cong pfB pfL)) (*◂-cong pfC pfU) (+-cong (*-cong pfC pfR) (*◂-cong pfD pfL))
◂-cong : ∀ {s} → {x y u v : Tri s} → x t≈ y → u t≈ v → x ◂ u t≈ y ◂ v
◂-cong one-eq one-eq = one-eq
◂-cong (two-eq pfU₁ pfR₁ pfL₁) (two-eq pfU₂ pfR₂ pfL₂) = two-eq (◂-cong pfU₁ pfU₂) (+-cong (◂*-cong pfU₁ pfR₂) (*◂-cong pfR₁ pfL₂)) (◂-cong pfL₁ pfL₂)

