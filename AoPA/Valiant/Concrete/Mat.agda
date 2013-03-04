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

_M++_ : ∀ {r c₁ c₂} → Mat r c₁ → Mat r c₂ → Mat r (deeper c₁ c₂)
Sing x M++ Sing y = RVec (two (one x) (one y))
Sing x M++ RVec v = RVec (two (one x) v)
RVec v M++ Sing x = RVec (two v (one x))
RVec u M++ RVec v = RVec (two u v)
CVec (two u v) M++ CVec (two u' v') = quad (cVec u) (cVec u') (cVec v) (cVec v')
CVec (two u v) M++ quad A B C D = quad (cVec u) (A M++ B) (cVec v) (C M++ D)
quad A B C D M++ CVec (two u v) = quad (A M++ B) (cVec u) (C M++ D) (cVec v)
quad A B C D M++ quad A' B' C' D' = quad (A M++ B) (A' M++ B') (C M++ D) (C' M++ D')

_over_ : ∀ {r₁ r₂ c} → Mat r₁ c → Mat r₂ c → Mat (deeper r₁ r₂) c
Sing x over Sing y = CVec (two (one x) (one y))
Sing x over CVec v = CVec (two (one x) v)
RVec (two u v) over RVec (two u' v') = quad (rVec u) (rVec v) (rVec u') (rVec v')
RVec (two u v) over quad A B C D = quad (rVec u) (rVec v) (A over C) (B over D)
CVec v over Sing x = CVec (two v (one x))
CVec u over CVec v = CVec (two u v)
quad A B C D over RVec (two u v) = quad (A over C) (B over D) (rVec u) (rVec v)
quad A B C D over quad A' B' C' D' = quad (A over C) (B over D) (A' over C') (B' over D')

left : ∀ {r c₁ c₂} → Mat r (deeper c₁ c₂) → Mat r c₁
left (RVec (two u v)) = rVec u
left (quad A B C D) = A over C

right : ∀ {r c₁ c₂} → Mat r (deeper c₁ c₂) → Mat r c₂
right (RVec (two u v)) = rVec v
right (quad A B C D) = B over D

upper : ∀ {r₁ r₂ c} → Mat (deeper r₁ r₂) c → Mat r₁ c
upper (CVec (two u v)) = cVec u
upper (quad A B C D) = A M++ B

lower : ∀ {r₁ r₂ c} → Mat (deeper r₁ r₂) c → Mat r₂ c
lower (CVec (two u v)) = cVec v
lower (quad A B C D) = C M++ D


unMat1 : ∀ {s} → Mat s one → Vec s
unMat1 (Sing x) = one x
unMat1 (CVec y) = y
unMat2 : ∀ {s} → Mat one s → Vec s
unMat2 (Sing x) = one x
unMat2 (RVec y) = y