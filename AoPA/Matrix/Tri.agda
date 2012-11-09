open import Relation.Binary.PropositionalEquality
open import Data.Product

import Matrix.Abstract
import Matrix.NewNewSplit


open import Matrix.NonAssociativeRing

open import Level using () renaming (zero to Lzero)

module Matrix.Tri (NAR : NonAssociativeRing Lzero Lzero) where


open Matrix.Abstract (NAR)
open Matrix.NewNewSplit (NAR)

data Tri : Splitting → Set where
  one : Tri one
  two : ∀ {s1 s2} -> Tri s1 -> SplitMat s1 s2 -> 
                                 Tri s2 -> 
                     Tri (deeper s1 s2)

T0 : ∀ {s} -> Tri s
T0 {one} = one
T0 {deeper y y'} = two T0 sZero T0

tvecmul : ∀ {s1} -> Tri s1 -> SplitVec s1 -> SplitVec s1
tvecmul {one} t v = one R0
tvecmul {deeper s₁ s₂} (two T₁ R T₂) (two v₁ v₂) = two (splitVecAdd (tvecmul T₁ v₁) (splitMatVecMul R v₂)) (tvecmul T₂ v₂)

vectmul : ∀ {s1} -> SplitVec s1 -> Tri s1 -> SplitVec s1
vectmul {one} t v = one R0
vectmul {deeper s₁ s₂} (two v₁ v₂) (two T₁ R T₂) = two (vectmul v₁ T₁) (splitVecAdd (splitVecMatMul v₁ R) (vectmul v₂ T₂))


_TS*_ : ∀ {s1 s2} -> Tri s1 -> SplitMat s1 s2 -> SplitMat s1 s2
_TS*_ {one} {one} t r = Sing R0
_TS*_ {deeper y y'} {one} T (CVec v) = CVec (tvecmul T v)
_TS*_ {one} {deeper y y'} t r = RVec zeroVec
_TS*_ {deeper s₁ s₂} {deeper t₁ t₂} (two T₁ R T₂) (quad A₁ A₂ A₃ A₄) = quad (splitAdd (T₁ TS* A₁) (splitMul R A₃)) (splitAdd (T₁ TS* A₂) (splitMul R A₄)) (T₂ TS* A₃) (T₂ TS* A₄)

_ST*_ : ∀ {s1 s2} ->  SplitMat s1 s2 -> Tri s2 -> SplitMat s1 s2
_ST*_ {one} {one} m t = Sing R0
_ST*_ {deeper s₁ s₂} {one} m one = CVec zeroVec
_ST*_ {one} {deeper s₁ s₂} (RVec v) T = RVec (vectmul v T)
_ST*_ {deeper s₁ s₂} {deeper t₁ t₂} (quad A B C D) (two T₁ R T₂) = quad (A ST* T₁) (splitAdd (splitMul A R) (B ST* T₂)) (C ST* T₁) (splitAdd (splitMul C R) (D ST* T₂))


--  A B  D E = AD (AE + BF)
--    C    F      CF
_T*_ : ∀ {s} -> Tri s -> Tri s -> Tri s
_T*_ one one = one
_T*_ (two T₁₁ R₁ T₁₂) (two T₂₁ R₂ T₂₂) = two (T₁₁ T* T₂₁) (splitAdd (T₁₁ TS* R₁) (R₁ ST* T₂₂)) (T₁₂ T* T₂₂)


_T+_ : ∀ {s} -> Tri s -> Tri s -> Tri s
_T+_ one one = one
_T+_ (two T₁₁ R₁ T₁₂) (two T₂₁ R₂ T₂₂) = two (T₁₁ T+ T₂₁) (splitAdd R₁ R₂) (T₁₂ T+ T₂₂)

⟨_,_,_⟩ : {a b c d : Set} -> 
        (a → b) → (a → c) → (a → d) →
        a → (b × c × d)
⟨ f , g , h ⟩ x = (f x , g x , h x)



tri1 : ∀ {s1 s2} -> Tri (deeper s1 s2) -> Tri s1
tri1 (two y y' y0) = y
tri2 : ∀ {s1 s2} -> Tri (deeper s1 s2) -> Tri s2
tri2 (two y y' y0) = y0
rec : ∀ {s1 s2} -> Tri (deeper s1 s2) -> SplitMat s1 s2
rec (two y y' y0) = y'
split : ∀ {s1 s2} -> Tri (deeper s1 s2) -> Tri s1 × SplitMat s1 s2 × Tri s2
split = ⟨ tri1 , rec , tri2 ⟩

unsplit : ∀ {s1 s2} -> Tri s1 × SplitMat s1 s2 × Tri s2 -> Tri (deeper s1 s2)
unsplit (T₁ , R , T₂) = two T₁ R T₂


unsplit∘split≡id : ∀ {s1 s2} (t : Tri (deeper s1 s2)) -> unsplit ( split t) ≡ t
unsplit∘split≡id (two T₁ R T₂) = refl


-- the triangles are supposed to be transitively closed!
valiantOverlap : ∀ {s1 s2} -> Tri s1 -> SplitMat s1 s2 -> Tri s2 -> SplitMat s1 s2
valiantOverlap {one} {one} A' C B' = C
valiantOverlap {one} {deeper s₁ s₂} A' (RVec v) B' = RVec (vectmul v B')
valiantOverlap {deeper s₁ s₂} {one} A' (CVec v) B' = CVec (tvecmul A' v)
valiantOverlap {deeper s₁ s₂} {deeper s₃ s₄} (two A₁ A₂ A₃) (quad C₂ C₄ C₁ C₃) (two B₃ B₂ B₁) = quad X₂ X₄ X₁ X₃
  where X₁ = valiantOverlap A₃ C₁ B₃
        X₂ = valiantOverlap A₁ (splitAdd C₂ (splitMul A₂ X₁)) B₃
        X₃ = valiantOverlap A₃ (splitAdd C₃ (splitMul X₁ B₂)) B₁
        X₄ = valiantOverlap A₁ (splitAdd C₄ (splitAdd (splitMul A₂ X₃) (splitMul X₂ B₂))) B₁

valiant : ∀ {s} -> Tri s -> Tri s
valiant one = one
valiant (two A C B) = two A' (valiantOverlap A' C B') B'
  where A' = (valiant A)
        B' = (valiant B)

foldTri : {s : Splitting} {b : Splitting -> Set} → (one' : b one) → (two' : ∀ {s1 s2} -> b s1 -> SplitMat s1 s2 -> b s2 -> b (deeper s1 s2) ) → Tri s → b s
foldTri one' two' one = one'
foldTri one' two' (two T₁ R T₂) = two' (foldTri one' two' T₁) R (foldTri one' two' T₂)


-- λ t1 r t2 -> two t1 (valiantOverlap t1 r t2) t2
valiantOverlap' : ∀ {s1 s2} -> Tri s1 -> SplitMat s1 s2 -> Tri s2 -> Tri (deeper s1 s2)
valiantOverlap' T₁ R T₂ = two T₁ (valiantOverlap T₁ R T₂) T₂

valiantFold : ∀ {s} → Tri s → Tri s
valiantFold = foldTri one valiantOverlap'


-- now, properties: 

-- t₁ (ttadd T₁ T₂) == ttadd (t₁ T₁) (t₁ T₂)
-- split (ttadd T₁ T₂) == ttadd (