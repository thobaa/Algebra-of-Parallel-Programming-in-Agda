-- module for concrete matrixes
-- Standard Library:

-- Own: 
open import Valiant.Abstract.NonAssociativeNonRing using (NonAssociativeNonRing)
open import Valiant.Concrete.Splitting using (Splitting; one; deeper)

module Valiant.Concrete.Mat {l₁ l₂} (NAR : NonAssociativeNonRing l₁ l₂) where
import Valiant.Helper.Definitions using (R; R0)
open Valiant.Helper.Definitions NAR


-- Concrete vector
data Vec : Splitting → Set l₁ where
  one : (x : R) → Vec one
  two : ∀ {s₁ s₂} → (u : Vec s₁)  → (v : Vec s₂) → Vec (deeper s₁ s₂)

zeroVec : ∀ {s} → Vec s
zeroVec {one} = one R0
zeroVec {deeper s₁ s₂} = two (zeroVec {s₁}) (zeroVec {s₂})


-- Concrete Matrix
data Mat : Splitting → Splitting → Set l₁ where
  Sing : (x : R)  → Mat one one
  RVec : ∀{s₁ s₂} → (v : Vec (deeper s₁ s₂)) → Mat one (deeper s₁ s₂)
  CVec : ∀{s₁ s₂} → (v : Vec (deeper s₁ s₂)) → Mat (deeper s₁ s₂) one
  quad : ∀{r₁ r₂ c₁ c₂} → (A : Mat r₁ c₁) → (B : Mat r₁ c₂) → 
                          (C : Mat r₂ c₁) → (D : Mat r₂ c₂) → 
                          Mat (deeper r₁ r₂) (deeper c₁ c₂)


-- zero matrix
zeroMat : ∀ {s1 s2} → Mat s1 s2
zeroMat {one} {one} = Sing R0
zeroMat {one} {deeper s₁ s₂} = RVec zeroVec
zeroMat {deeper s₁ s₂} {one} = CVec zeroVec
zeroMat {deeper s₁ s₂} {deeper s₁' s₂'} = quad zeroMat zeroMat zeroMat zeroMat 


-- helper functions (constructors)
cVec : ∀ {s} → Vec s → Mat s one
cVec {one} (one x) = Sing x
cVec {deeper y y'} v = CVec v
rVec : ∀ {s} → Vec s → Mat one s
rVec {one} (one x) = Sing x
rVec {deeper y y'} v = RVec v

unMat1 : ∀ {s} → Mat s one → Vec s
unMat1 (Sing x) = one x
unMat1 (CVec y) = y
unMat2 : ∀ {s} → Mat one s → Vec s
unMat2 (Sing x) = one x
unMat2 (RVec y) = y