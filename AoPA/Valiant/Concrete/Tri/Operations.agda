open import Valiant.Abstract.NonAssociativeNonRing
open import Valiant.Concrete.Splitting
import Valiant.Concrete.Mat


module Valiant.Concrete.Tri.Operations {l₁ l₂} (NAR : NonAssociativeNonRing l₁ l₂) where

import Valiant.Concrete.Tri
import Valiant.Concrete.Mat
import Valiant.Helper.Definitions
import Valiant.Concrete.Mat.Operations
open Valiant.Concrete.Tri NAR
open Valiant.Concrete.Mat.Operations NAR
open Valiant.Concrete.Mat NAR
open Valiant.Helper.Definitions NAR

 
infix 6 _◂|_
_◂|_ : ∀ {s₁} -> Tri s₁ -> Vec s₁ -> Vec s₁
_◂|_ {one} t v = one R0
_◂|_ {deeper s₁ s₂} (two T₁ R T₂) (two v₁ v₂) = two (T₁ ◂| v₁  ⊕  R *| v₂) (T₂ ◂| v₂)

infix 6 _|◂_
_|◂_ : ∀ {s₁} -> Vec s₁ -> Tri s₁ -> Vec s₁
_|◂_ {one} t v = one R0
_|◂_ {deeper s₁ s₂} (two v₁ v₂) (two T₁ R T₂) = two (v₁ |◂ T₁) (v₁ |* R  ⊕  v₂ |◂ T₂)


infix 6 _◂*_
_◂*_ : ∀ {s₁ s₂} -> Tri s₁ -> Mat s₁ s₂ -> Mat s₁ s₂
_◂*_ {one} {one} t r = Sing R0
_◂*_ {deeper y y'} {one} T (CVec v) = CVec (T ◂| v)
_◂*_ {one} {deeper y y'} t r = RVec zeroVec
_◂*_ {deeper s₁ s₂} {deeper t₁ t₂} (two T₁ R T₂) (quad A₁ A₂ A₃ A₄) = quad (T₁ ◂* A₁  +  R * A₃) (T₁ ◂* A₂  +  R * A₄) (T₂ ◂* A₃) (T₂ ◂* A₄)

infix 6 _*◂_
_*◂_ : ∀ {s₁ s₂} ->  Mat s₁ s₂ -> Tri s₂ -> Mat s₁ s₂
_*◂_ {one} {one} m t = Sing R0
_*◂_ {deeper s₁ s₂} {one} m one = CVec zeroVec
_*◂_ {one} {deeper s₁ s₂} (RVec v) T = RVec (v |◂ T)
_*◂_ {deeper s₁ s₂} {deeper t₁ t₂} (quad A B C D) (two T₁ R T₂) = quad (A *◂ T₁) (A * R  +  B *◂ T₂) (C *◂ T₁) (C * R  +  D *◂ T₂)


--  A B  D E = AD (AE + BF)
--    C    F      CF
infix 6 _◂_
_◂_ : ∀ {s} -> Tri s -> Tri s -> Tri s
_◂_ one one = one
_◂_ (two T₁₁ R₁ T₁₂) (two T₂₁ R₂ T₂₂) = two (T₁₁ ◂ T₂₁) (T₁₁ ◂* R₂  +  R₁ *◂ T₂₂) (T₁₂ ◂ T₂₂)

infix 5 _◂+_
_◂+_ : ∀ {s} -> Tri s -> Tri s -> Tri s
_◂+_ one one = one
_◂+_ (two T₁₁ R₁ T₁₂) (two T₂₁ R₂ T₂₂) = two (T₁₁ ◂+ T₂₁) (R₁ + R₂) (T₁₂ ◂+ T₂₂)

