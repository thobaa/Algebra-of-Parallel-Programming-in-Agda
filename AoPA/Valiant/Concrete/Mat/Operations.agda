-- module for concrete matrixes
open import Data.Nat using ()
open import Data.Fin using (Fin; fromℕ; fromℕ≤; toℕ;  raise; reduce≥) 
                     renaming (zero to f0; suc to fsuc)

open import Data.Integer using (ℤ; +_; _-_)
--open import Data.Vec renaming (Vec to SVec; [_] to <_>)
open import Valiant.MatrixAlgebra.Definitions using (toℤ) renaming (_≥_ to _z≥_; _<_ to _z<_)


open import Valiant.Concrete.Splitting
open import Valiant.Abstract.NonAssociativeNonRing
import Valiant.Concrete.Mat as Mat
import Valiant.Helper.Definitions
module Valiant.Concrete.Mat.Operations {l₁ l₂} (NAR : NonAssociativeNonRing l₁ l₂) where

open Mat NAR
open Valiant.Helper.Definitions NAR

-- slightly lower than multiplication of scalars
--infixl 
infix 6 _∙_
_∙_ : ∀ {t1} → Vec t1 → Vec t1 → R
_∙_ {one} (one x) (one x') = x R* x'
_∙_ {deeper y y'} (two y0 y1) (two y2 y3) = (y0 ∙ y2)  R+  (y1 ∙ y3)



infix 6 _⊛|_
_⊛|_ : ∀ {s} → R → Vec s → Vec s
_⊛|_ x (one x') = one (x R* x')
_⊛|_ x (two v₁ v₂) = two (x ⊛| v₁) (x ⊛| v₂)

infix 6 _|⊛_
_|⊛_ : ∀ {s} → Vec s → R → Vec s
_|⊛_ (one x) x' = one (x R* x')
_|⊛_ (two v₁ v₂) x = two (v₁ |⊛ x) (v₂ |⊛ x)

-- exterior product:
_⊛_ : ∀ {s₁ s₂} → Vec s₁ → Vec s₂ → Mat s₁ s₂
one x ⊛ one y = Sing (x R* y)
one x ⊛ two u v = RVec (two (x ⊛| u) (x ⊛| v))
two u v ⊛ one x = CVec (two (u |⊛ x) (v |⊛ x))
two u₁ v₁ ⊛ two u₂ v₂ = quad (u₁ ⊛ u₂) (u₁ ⊛ v₂) (v₁ ⊛ u₂) (v₁ ⊛ v₂)


infix 5 _⊕_
_⊕_ : ∀ {rs} → Vec rs → Vec rs → Vec rs
_⊕_ {one} (one x) (one x') = one (x R+ x')
_⊕_ {deeper s₁ s₂} (two v₁ v₂) (two u₁ u₂) = two (v₁ ⊕ u₁) (v₂ ⊕ u₂)

infix 5 _+_
_+_ : ∀ {rs cs} → Mat rs cs → Mat rs cs → Mat rs cs
_+_ {one} {one} (Sing x) (Sing x') = Sing (x R+ x')
_+_ {one} {deeper s₁ s₂} (RVec u) (RVec v) = RVec (u ⊕ v)
_+_ {deeper s₁ s₂} {one} (CVec u) (CVec v) = CVec (u ⊕ v)
_+_ {deeper s₁ s₂} {deeper t₁ t₂} (quad A₁ B₁ C₁ D₁) (quad A₂ B₂ C₂ D₂) = quad (A₁ + A₂) (B₁ + B₂) (C₁ + C₂) (D₁ + D₂)


infix 6 _*|_
_*|_ : ∀ {t1 t2} → Mat t1 t2 → Vec t2 → Vec t1
_*|_ (Sing x) (one x') = one (x R* x')
_*|_ (RVec y) v = one (y ∙ v)
_*|_ (CVec y) (one x) = y |⊛ x
_*|_ (quad A B C D) (two v₁ v₂) = two ((A *| v₁) ⊕ (B *| v₂)) ((C *| v₁) ⊕ (D *| v₂))

infix 6 _|*_
_|*_ : ∀ {t1 t2} → Vec t1 → Mat t1 t2 → Vec t2
_|*_  (one x) (Sing x') = one (x R* x')
_|*_ (one x) (RVec y) = x ⊛| y
_|*_ u (CVec v) = one (u ∙ v) 
_|*_ (two v₁ v₂) (quad A B C D) = two ((v₁ |* A) ⊕ (v₂ |* C)) ((v₁ |* B) ⊕ (v₂ |* D))


infix 6 _*_
_*_ : ∀ {t1 t2 t3} → Mat t1 t2 → Mat t2 t3 → Mat t1 t3
_*_ {one} {one} {one} (Sing x) (Sing x') = Sing (x R* x')
_*_ {one} {one} {deeper t₁ t₂} (Sing x) (RVec v) = RVec (x ⊛| v)
_*_ {deeper s₁ s₂} {one} (CVec y) (Sing x) = CVec (y |⊛ x)
_*_ {deeper s₁ s₂} {one} {deeper t₁ t₂} (CVec (two u₁ u₂)) (RVec (two v₁ v₂)) = quad (u₁ ⊛ v₁) (u₁ ⊛ v₂) (u₂ ⊛ v₁) (u₂ ⊛ v₂) -- or just u ⊛ v  --((cVec u₁) * (rVec v₁)) ((cVec u₁) * (rVec v₂)) ((cVec u₂) * (rVec v₁)) ((cVec u₂) * (rVec v₂))
_*_ {one} {deeper s₁ s₂} (RVec u) (CVec v) = Sing (u ∙ v)
_*_ {one} {deeper s₁ s₂} (RVec (two u v)) (quad A B C D) = RVec (two (u |* A ⊕ v |* C) (u |* B ⊕ v |* D)) --(two (unMat2 (rVec u * A  +  rVec v * C)) (unMat2 (rVec u * B  +  rVec v * D)))
_*_ {deeper r1 r2} {deeper y y'} (quad A B C D) (CVec (two e f)) = CVec (two (A *| e ⊕ B *| f) (C *| e ⊕ D *| f)) --(two (unMat1 (A * cVec e  +  B * cVec f)) (unMat1 (C * cVec e  +  D * cVec f)))
_*_ {deeper r1 r2} {deeper y y'} (quad A₁ B₁ C₁ D₁) (quad A₂ B₂ C₂ D₂) = quad (A₁ * A₂  +  B₁ * C₂) (A₁ * B₂  +  B₁ * D₂) (C₁ * A₂  +  D₁ * C₂) (C₁ * B₂  +  D₁ * D₂)

