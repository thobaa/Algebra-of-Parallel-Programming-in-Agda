open import Valiant.Abstract.NonAssociativeNonRing
open import Data.Product using (proj₁; proj₂; Σ; _,_)

open import Valiant.Concrete.Splitting

module Valiant.Concrete.Tri.Zeros {l₁ l₂} (NAR : NonAssociativeNonRing l₁ l₂) where

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
open Valiant.Concrete.Mat.Properties NAR renaming (commutativeMonoid to cmm; v-commutativeMonoid to cmv)

import Valiant.Concrete.Tri.Equalities 
open Valiant.Concrete.Tri.Equalities NAR
import Valiant.Concrete.Tri.CommutativeMonoid
open Valiant.Concrete.Tri.CommutativeMonoid NAR

open NonAssociativeNonRing NAR using (_≈_) renaming (refl to ≈refl; sym to ≈sym; trans to ≈trans; +-assoc to R+-assoc; +-comm to R+-comm; +-identity to R+-identity; +-cong to R+-cong; *-cong to R*-cong; distrib to R-distrib; +-commutativeMonoid to cmr; zero to R-zero)

∙-zeroˡ : ∀ {s} (v : Vec s) → zeroVec ∙ v ≈ R0
∙-zeroˡ (one x) = proj₁ R-zero x
∙-zeroˡ (two u v) = sumLemma {cm = cmr} (∙-zeroˡ u) (∙-zeroˡ v)
∙-zeroʳ : ∀ {s} (v : Vec s) → v ∙ zeroVec ≈ R0
∙-zeroʳ (one x) = proj₂ R-zero x
∙-zeroʳ (two u v) = sumLemma {cm = cmr} (∙-zeroʳ u) (∙-zeroʳ v)

|⊛-zeroˡ : ∀ {s} (x : R) → zeroVec {s} |⊛ x v≈ zeroVec
|⊛-zeroˡ {one} x = one-eq (proj₁ R-zero x)
|⊛-zeroˡ {deeper s₁ s₂} x = two-eq (|⊛-zeroˡ x) (|⊛-zeroˡ x)
|⊛-zeroʳ : ∀ {s} (v : Vec s) → v |⊛ R0 v≈ zeroVec
|⊛-zeroʳ (one x) = one-eq (proj₂ R-zero x)
|⊛-zeroʳ (two u v) = two-eq (|⊛-zeroʳ u) (|⊛-zeroʳ v)
⊛|-zeroˡ : ∀ {s} (v : Vec s) → R0 ⊛| v v≈ zeroVec
⊛|-zeroˡ (one x) = one-eq (proj₁ R-zero x)
⊛|-zeroˡ (two u v) = two-eq (⊛|-zeroˡ u) (⊛|-zeroˡ v)
⊛|-zeroʳ : ∀ {s} (x : R) → x ⊛| zeroVec {s} v≈ zeroVec
⊛|-zeroʳ {one} x = one-eq (proj₂ R-zero x)
⊛|-zeroʳ {deeper s₁ s₂} x = two-eq (⊛|-zeroʳ x) (⊛|-zeroʳ x)

⊛-zeroˡ : ∀ {s₁ s₂} (v : Vec s₂) → zeroVec {s₁} ⊛ v m≈ zeroMat 
⊛-zeroˡ {one} (one x) = Sing-eq (proj₁ R-zero x)
⊛-zeroˡ {one} (two u v) = RVec-eq (two-eq (⊛|-zeroˡ u) (⊛|-zeroˡ v))
⊛-zeroˡ {deeper s₁ s₂} (one x) = CVec-eq (two-eq (|⊛-zeroˡ x) (|⊛-zeroˡ x))
⊛-zeroˡ {deeper s₁ s₂} (two u v) = quad-eq (⊛-zeroˡ u) (⊛-zeroˡ v) (⊛-zeroˡ u) (⊛-zeroˡ v)
⊛-zeroʳ : ∀ {s₁ s₂} (v : Vec s₁) → v ⊛ zeroVec {s₂} m≈ zeroMat 
⊛-zeroʳ {one} {one} (one x) = Sing-eq (proj₂ R-zero x)
⊛-zeroʳ {(deeper s₁ s₂)} {one} (two u v) = CVec-eq (two-eq (|⊛-zeroʳ u) (|⊛-zeroʳ v))
⊛-zeroʳ {one} {deeper s₁ s₂} (one x) = RVec-eq (two-eq (⊛|-zeroʳ x) (⊛|-zeroʳ x))
⊛-zeroʳ {(deeper s₁ s₂)} {deeper s₁' s₂'} (two u v) = quad-eq (⊛-zeroʳ u) (⊛-zeroʳ u) (⊛-zeroʳ v) (⊛-zeroʳ v)


*|-zeroˡ : ∀ {s₁ s₂} (v : Vec s₂) → zeroMat {s₁} {s₂} *| v v≈ zeroVec
*|-zeroˡ {one} (one x) = one-eq (proj₁ R-zero x)
*|-zeroˡ {deeper s₁ s₂} (one x) = two-eq (|⊛-zeroˡ x) (|⊛-zeroˡ x)
*|-zeroˡ {one} (two u v) = one-eq (sumLemma {cm = cmr} (∙-zeroˡ u) (∙-zeroˡ v))
*|-zeroˡ {deeper s₁ s₂} (two u v) = two-eq (sumLemma {cm = cmv} (*|-zeroˡ u) (*|-zeroˡ v)) (sumLemma {cm = cmv} (*|-zeroˡ u) (*|-zeroˡ v))
*|-zeroʳ : ∀ {s₁ s₂} (x : Mat s₁ s₂) → x *| zeroVec v≈ zeroVec
*|-zeroʳ (Sing x) = one-eq (proj₂ R-zero x)
*|-zeroʳ (CVec v) = |⊛-zeroʳ v
*|-zeroʳ (RVec (two u v)) = one-eq (sumLemma {cm = cmr} (∙-zeroʳ u) (∙-zeroʳ v))
*|-zeroʳ (quad A B C D) = two-eq (sumLemma {cm = cmv} (*|-zeroʳ A) (*|-zeroʳ B)) (sumLemma {cm = cmv} (*|-zeroʳ C) (*|-zeroʳ D))

|*-zeroˡ : ∀ {s₁ s₂} (x : Mat s₁ s₂) → zeroVec |* x v≈ zeroVec
|*-zeroˡ (Sing x) = one-eq (proj₁ R-zero x)
|*-zeroˡ (RVec (two u v)) = two-eq (⊛|-zeroˡ u) (⊛|-zeroˡ v)
|*-zeroˡ (CVec (two u v)) = one-eq (sumLemma {cm = cmr} (∙-zeroˡ u) (∙-zeroˡ v))
|*-zeroˡ (quad A B C D) = two-eq (sumLemma {cm = cmv} (|*-zeroˡ A) (|*-zeroˡ C)) (sumLemma {cm = cmv} (|*-zeroˡ B) (|*-zeroˡ D))
|*-zeroʳ : ∀ {s₁ s₂} (v : Vec s₁) → v |* zeroMat {s₁} {s₂} v≈ zeroVec
|*-zeroʳ {one} {one} (one x) = one-eq (proj₂ R-zero x)
|*-zeroʳ {(deeper s₁ s₂)} {one} (two u v) = one-eq (sumLemma {cm = cmr} (∙-zeroʳ u) (∙-zeroʳ v))
|*-zeroʳ {one} {deeper s₁ s₂} (one x) = two-eq (⊛|-zeroʳ x) (⊛|-zeroʳ x)
|*-zeroʳ {(deeper s₁ s₂)} {deeper s₁' s₂'} (two u v) = two-eq (sumLemma {cm = cmv} (|*-zeroʳ u) (|*-zeroʳ v)) (sumLemma {cm = cmv} (|*-zeroʳ u) (|*-zeroʳ v))


◂|-zeroˡ : ∀ {s} (v : Vec s) → zeroTri ◂| v v≈ zeroVec
◂|-zeroˡ (one x) = v-refl
◂|-zeroˡ (two u v) = two-eq (sumLemma {cm = cmv} (◂|-zeroˡ u) (*|-zeroˡ v)) (◂|-zeroˡ v)
◂|-zeroʳ : ∀ {s} (x : Tri s) → x ◂| zeroVec v≈ zeroVec
◂|-zeroʳ one = v-refl
◂|-zeroʳ (two U R L) = two-eq (sumLemma {cm = cmv} (◂|-zeroʳ U) (*|-zeroʳ R)) (◂|-zeroʳ L)
|◂-zeroˡ : ∀ {s} (x : Tri s) → zeroVec |◂ x v≈ zeroVec
|◂-zeroˡ one = v-refl
|◂-zeroˡ (two U R L) = two-eq (|◂-zeroˡ U) (sumLemma {cm = cmv} (|*-zeroˡ R) (|◂-zeroˡ L))
|◂-zeroʳ : ∀ {s} (v : Vec s) → v |◂ zeroTri v≈ zeroVec
|◂-zeroʳ (one x) = v-refl
|◂-zeroʳ (two u v) = two-eq (|◂-zeroʳ u) (sumLemma {cm = cmv} (|*-zeroʳ u) (|◂-zeroʳ v))


*-zeroˡ : ∀ {s₁ s₂ s₃} (A : Mat s₂ s₃) → zeroMat {s₁} {s₂} * A m≈ zeroMat
*-zeroˡ {one} (Sing x) = Sing-eq (proj₁ R-zero x)
*-zeroˡ {deeper s₁ s₂} (Sing x) = CVec-eq (two-eq (|⊛-zeroˡ x) (|⊛-zeroˡ x))
*-zeroˡ {one} (RVec (two u v)) = RVec-eq (two-eq (⊛|-zeroˡ u) (⊛|-zeroˡ v))
*-zeroˡ {deeper s₁ s₂} (RVec (two u v)) = quad-eq (⊛-zeroˡ u) (⊛-zeroˡ v) (⊛-zeroˡ u) (⊛-zeroˡ v)
*-zeroˡ {one} (CVec v) = Sing-eq (∙-zeroˡ v)
*-zeroˡ {deeper s₁ s₂} (CVec (two u v)) = CVec-eq (two-eq (sumLemma {cm = cmv} (*|-zeroˡ u) (*|-zeroˡ v)) (sumLemma {cm = cmv} (*|-zeroˡ u) (*|-zeroˡ v)))
*-zeroˡ {one} (quad A B C D) = RVec-eq (two-eq (sumLemma {cm = cmv} (|*-zeroˡ A) (|*-zeroˡ C)) (sumLemma {cm = cmv} (|*-zeroˡ B) (|*-zeroˡ D)))
*-zeroˡ {deeper s₁ s₂} (quad A B C D) = quad-eq (sumLemma {cm = cmm} (*-zeroˡ A) (*-zeroˡ C)) (sumLemma {cm = cmm} (*-zeroˡ B) (*-zeroˡ D)) (sumLemma {cm = cmm} (*-zeroˡ A) (*-zeroˡ C)) (sumLemma {cm = cmm} (*-zeroˡ B) (*-zeroˡ D))
*-zeroʳ : ∀ {s₁ s₂ s₃} (A : Mat s₁ s₂) → A * zeroMat {s₂} {s₃} m≈ zeroMat
*-zeroʳ {one} {one} {one} (Sing x) = Sing-eq (proj₂ R-zero x)
*-zeroʳ {one} {deeper s₁ s₂} {one} (RVec (two u v)) = Sing-eq (sumLemma {cm = cmr} (∙-zeroʳ u) (∙-zeroʳ v))
*-zeroʳ {deeper s₁ s₂} {one} {one} (CVec (two u v)) = CVec-eq (two-eq (|⊛-zeroʳ u) (|⊛-zeroʳ v))
*-zeroʳ {(deeper r₁ r₂)} {(deeper c₁ c₂)} {one} (quad A B C D) = CVec-eq (two-eq (sumLemma {cm = cmv} (*|-zeroʳ A) (*|-zeroʳ B)) (sumLemma {cm = cmv} (*|-zeroʳ C) (*|-zeroʳ D)))
*-zeroʳ {one} {one} {deeper s₁' s₂'} (Sing x) = RVec-eq (two-eq (⊛|-zeroʳ x) (⊛|-zeroʳ x))
*-zeroʳ {one} {deeper s₁ s₂} {deeper s₁' s₂'} (RVec (two u v)) = RVec-eq (two-eq (sumLemma {cm = cmv} (|*-zeroʳ u) (|*-zeroʳ v)) (sumLemma {cm = cmv} (|*-zeroʳ u) (|*-zeroʳ v)))
*-zeroʳ {deeper s₁ s₂} {one} {deeper s₁' s₂'} (CVec (two u v)) = quad-eq (⊛-zeroʳ u) (⊛-zeroʳ u) (⊛-zeroʳ v) (⊛-zeroʳ v)
*-zeroʳ {(deeper r₁ r₂)} {(deeper c₁ c₂)} {deeper s₁' s₂'} (quad A B C D) = quad-eq (sumLemma {cm = cmm} (*-zeroʳ A) (*-zeroʳ B)) (sumLemma {cm = cmm} (*-zeroʳ A) (*-zeroʳ B)) (sumLemma {cm = cmm} (*-zeroʳ C) (*-zeroʳ D)) (sumLemma {cm = cmm} (*-zeroʳ C) (*-zeroʳ D)) 

◂*-zeroˡ : {s₁ s₂ : _} → (x : Mat s₁ s₂) → zeroTri ◂* x m≈ zeroMat
◂*-zeroˡ (Sing x) = Sing-eq ≈refl
◂*-zeroˡ (RVec v) = m-refl
◂*-zeroˡ (CVec (two u v)) = CVec-eq (two-eq (sumLemma {cm = cmv} (◂|-zeroˡ u) (*|-zeroˡ v)) (◂|-zeroˡ v))
◂*-zeroˡ (quad A B C D) = quad-eq (sumLemma {cm = cmm} (◂*-zeroˡ A) (*-zeroˡ C)) (sumLemma {cm = cmm} (◂*-zeroˡ B) (*-zeroˡ D)) (◂*-zeroˡ C) (◂*-zeroˡ D)

*◂-zeroˡ : {s₁ s₂ : _} → (x : Tri s₂) → zeroMat {s₁} {s₂}*◂ x m≈ zeroMat
*◂-zeroˡ {one} {one} one = Sing-eq ≈refl
*◂-zeroˡ {deeper s₁ s₂} {one} one = CVec-eq v-refl
*◂-zeroˡ {one} {deeper s₁ s₂} (two U R L) = RVec-eq (two-eq (|◂-zeroˡ U) (sumLemma {cm = cmv} (|*-zeroˡ R) (|◂-zeroˡ L)))
*◂-zeroˡ {deeper s₁ s₂} {deeper s₁' s₂'} (two U R L) = quad-eq (*◂-zeroˡ U) (sumLemma {cm = cmm} (*-zeroˡ R) (*◂-zeroˡ L)) (*◂-zeroˡ U) (sumLemma {cm = cmm} (*-zeroˡ R) (*◂-zeroˡ L))


◂*-zeroʳ : {s₁ s₂ : _} → (x : Tri s₁) → x ◂* zeroMat {s₁} {s₂} m≈ zeroMat
◂*-zeroʳ {one} {one} one = Sing-eq ≈refl
◂*-zeroʳ {deeper s₁ s₂} {one} (two U R L) = CVec-eq (two-eq (sumLemma {cm = cmv} (◂|-zeroʳ U) (*|-zeroʳ R)) (◂|-zeroʳ L))
◂*-zeroʳ {one} {deeper s₁ s₂} one = RVec-eq (two-eq v-refl v-refl)
◂*-zeroʳ {deeper s₁ s₂} {deeper s₁' s₂'} (two U R L) = quad-eq (sumLemma {cm = cmm} (◂*-zeroʳ U) (*-zeroʳ R)) (sumLemma {cm = cmm} (◂*-zeroʳ U) (*-zeroʳ R)) (◂*-zeroʳ L) (◂*-zeroʳ L)

*◂-zeroʳ : {s₁ s₂ : _} → (x : Mat s₁ s₂) → x *◂ zeroTri m≈ zeroMat
*◂-zeroʳ (Sing x) = Sing-eq ≈refl
*◂-zeroʳ (RVec (two u v)) = RVec-eq (two-eq (|◂-zeroʳ u) (sumLemma {cm = cmv} (|*-zeroʳ u) (|◂-zeroʳ v)))
*◂-zeroʳ (CVec (two u v)) = CVec-eq (two-eq v-refl v-refl)
*◂-zeroʳ (quad A B C D) = quad-eq (*◂-zeroʳ A) (sumLemma {cm = cmm} (*-zeroʳ A) (*◂-zeroʳ B)) (*◂-zeroʳ C) (sumLemma {cm = cmm} (*-zeroʳ C) (*◂-zeroʳ D))

◂-zeroˡ : {s : _} → (x : Tri s) → zeroTri ◂ x t≈ zeroTri
◂-zeroˡ one = one-eq
◂-zeroˡ (two U R L) = two-eq (◂-zeroˡ U) (sumLemma {cm = cmm} (◂*-zeroˡ R) (*◂-zeroˡ L))
                                                  (◂-zeroˡ L)
◂-zeroʳ : {s : _} → (x : Tri s) → x ◂ zeroTri t≈ zeroTri
◂-zeroʳ one = one-eq
◂-zeroʳ (two U R L) = two-eq (◂-zeroʳ U) (sumLemma {cm = cmm} (◂*-zeroʳ U) (*◂-zeroʳ R)) (◂-zeroʳ L)