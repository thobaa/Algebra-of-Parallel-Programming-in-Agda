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

tZero : ∀ {s} -> Tri s
tZero {one} = one
tZero {deeper y y'} = two tZero sZero tZero

tvecmul : ∀ {s1} -> Tri s1 -> SplitVec s1 -> SplitVec s1
tvecmul {one} t v = one R0
tvecmul {deeper s₁ s₂} (two T₁ R T₂) (two v₁ v₂) = two (splitVecAdd (tvecmul T₁ v₁) (splitMatVecMul R v₂)) (tvecmul T₂ v₂)

vectmul : ∀ {s1} -> SplitVec s1 -> Tri s1 -> SplitVec s1
vectmul {one} t v = one R0
vectmul {deeper s₁ s₂} (two v₁ v₂) (two T₁ R T₂) = two (vectmul v₁ T₁) (splitVecAdd (splitVecMatMul v₁ R) (vectmul v₂ T₂))

trmul : ∀ {s1 s2} -> Tri s1 -> SplitMat s1 s2 -> SplitMat s1 s2
trmul {one} {one} t r = Sing R0
trmul {deeper y y'} {one} T (CVec v) = CVec (tvecmul T v)
trmul {one} {deeper y y'} t r = RVec zeroVec
trmul {deeper s₁ s₂} {deeper t₁ t₂} (two T₁ R T₂) (quad A₁ A₂ A₃ A₄) = quad (splitAdd (trmul T₁ A₁) (splitMul R A₃)) (splitAdd (trmul T₁ A₂) (splitMul R A₄)) (trmul T₂ A₃) (trmul T₂ A₄)

rtmul : ∀ {s1 s2} ->  SplitMat s1 s2 -> Tri s2 -> SplitMat s1 s2
rtmul {one} {one} m t = Sing R0
rtmul {deeper s₁ s₂} {one} m one = CVec zeroVec
rtmul {one} {deeper s₁ s₂} (RVec v) T = RVec (vectmul v T)
rtmul {deeper s₁ s₂} {deeper t₁ t₂} (quad A B C D) (two T₁ R T₂) = quad (rtmul A T₁) (splitAdd (splitMul A R) (rtmul B T₂)) (rtmul C T₁) (splitAdd (splitMul C R) (rtmul D T₂))


--  A B  D E = AD (AE + BF)
--    C    F      CF
ttmul : ∀ {s} -> Tri s -> Tri s -> Tri s
ttmul {one} t1 t2 = one
ttmul {deeper y y'} (two T₁₁ R₁ T₁₂) (two T₂₁ R₂ T₂₂) = two (ttmul T₁₁ T₂₁) (splitAdd (trmul T₁₁ R₁) (rtmul R₁ T₂₂)) (ttmul T₁₂ T₂₂)


ttadd : ∀ {s} -> Tri s -> Tri s -> Tri s
ttadd {one} t1 t2 = one
ttadd {deeper s₁ s₂} (two T₁₁ R₁ T₁₂) (two T₂₁ R₂ T₂₂) = two (ttadd T₁₁ T₂₁) (splitAdd R₁ R₂) (ttadd T₁₂ T₂₂)

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
        X₄ = valiantOverlap A₁ (splitAdd (splitMul A₂ X₃) (splitMul X₂ B₂)) B₁

valiant : ∀ {s} -> Tri s -> Tri s
valiant one = one
valiant (two A C B) = two A' (valiantOverlap A' C B') B'
  where A' = (valiant A)
        B' = (valiant B)


-- now, properties: 

-- t₁ (ttadd T₁ T₂) == ttadd (t₁ T₁) (t₁ T₂)
-- split (ttadd T₁ T₂) == ttadd (