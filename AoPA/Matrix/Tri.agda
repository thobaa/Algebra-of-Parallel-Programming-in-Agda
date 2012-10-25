module Matrix.Tri where

open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Matrix.Abstract
open import Matrix.NewNewSplit

data Tri (a : Ring') : Splitting → Set where
  one : Tri a one
  two : ∀ {s1 s2} -> Tri a s1 -> SplitMat a s1 s2 -> 
                                 Tri a s2 -> 
                     Tri a (deeper s1 s2)

tZero : ∀ {a s} -> Tri a s
tZero {a} {one} = one
tZero {a} {deeper y y'} = two tZero sZero tZero

tvecmul : ∀ {a s1} -> Tri a s1 -> SplitVec a s1 -> SplitVec a s1
tvecmul {a} {one} t v = one (R0 a)
tvecmul {a} {deeper s₁ s₂} (two T₁ R T₂) (two v₁ v₂) = two (splitVecAdd (tvecmul T₁ v₁) (splitMatVecMul R v₂)) (tvecmul T₂ v₂)

vectmul : ∀ {a s1} -> SplitVec a s1 -> Tri a s1 -> SplitVec a s1
vectmul {a} {one} t v = one (R0 a)
vectmul {a} {deeper s₁ s₂} (two v₁ v₂) (two T₁ R T₂) = two (vectmul v₁ T₁) (splitVecAdd (splitVecMatMul v₁ R) (vectmul v₂ T₂))

trmul : ∀ {a s1 s2} -> Tri a s1 -> SplitMat a s1 s2 -> SplitMat a s1 s2
trmul {a} {one} {one} t r = Sing (R0 a)
trmul {a} {deeper y y'} {one} T (CVec v) = CVec (tvecmul T v)
trmul {a} {one} {deeper y y'} t r = RVec zeroVec
trmul {a} {deeper s₁ s₂} {deeper t₁ t₂} (two T₁ R T₂) (quad A₁ A₂ A₃ A₄) = quad (splitAdd (trmul T₁ A₁) (splitMul R A₃)) (splitAdd (trmul T₁ A₂) (splitMul R A₄)) (trmul T₂ A₃) (trmul T₂ A₄)

rtmul : ∀ {a s1 s2} ->  SplitMat a s1 s2 -> Tri a s2 -> SplitMat a s1 s2
rtmul {a} {one} {one} m t = Sing (R0 a)
rtmul {a} {deeper s₁ s₂} {one} m one = CVec zeroVec
rtmul {a} {one} {deeper s₁ s₂} (RVec v) T = RVec (vectmul v T)
rtmul {a} {deeper s₁ s₂} {deeper t₁ t₂} (quad A B C D) (two T₁ R T₂) = quad (rtmul A T₁) (splitAdd (splitMul A R) (rtmul B T₂)) (rtmul C T₁) (splitAdd (splitMul C R) (rtmul D T₂))


--  A B  D E = AD (AE + BF)
--    C    F      CF
ttmul : ∀ {a s} -> Tri a s -> Tri a s -> Tri a s
ttmul {a} {one} t1 t2 = one
ttmul {a} {deeper y y'} (two T₁₁ R₁ T₁₂) (two T₂₁ R₂ T₂₂) = two (ttmul T₁₁ T₂₁) (splitAdd (trmul T₁₁ R₁) (rtmul R₁ T₂₂)) (ttmul T₁₂ T₂₂)


ttadd : ∀ {a s} -> Tri a s -> Tri a s -> Tri a s
ttadd {a} {one} t1 t2 = one
ttadd {a} {deeper s₁ s₂} (two T₁₁ R₁ T₁₂) (two T₂₁ R₂ T₂₂) = two (ttadd T₁₁ T₂₁) (splitAdd R₁ R₂) (ttadd T₁₂ T₂₂)

⟨_,_,_⟩ : {a b c d : Set} -> 
        (a → b) → (a → c) → (a → d) →
        a → (b × c × d)
⟨ f , g , h ⟩ x = (f x , g x , h x)



tri1 : ∀ {a s1 s2} -> Tri a (deeper s1 s2) -> Tri a s1
tri1 (two y y' y0) = y
tri2 : ∀ {a s1 s2} -> Tri a (deeper s1 s2) -> Tri a s2
tri2 (two y y' y0) = y0
rec : ∀ {a s1 s2} -> Tri a (deeper s1 s2) -> SplitMat a s1 s2
rec (two y y' y0) = y'
split : ∀ {a s1 s2} -> Tri a (deeper s1 s2) -> Tri a s1 × SplitMat a s1 s2 × Tri a s2
split = ⟨ tri1 , rec , tri2 ⟩

unsplit : ∀ {a s1 s2} -> Tri a s1 × SplitMat a s1 s2 × Tri a s2 -> Tri a (deeper s1 s2)
unsplit (T₁ , R , T₂) = two T₁ R T₂


unsplit∘split≡id : ∀ {a s1 s2} (t : Tri a (deeper s1 s2)) -> unsplit ( split t) ≡ t
unsplit∘split≡id (two T₁ R T₂) = refl

-- now, properties: 

-- t₁ (ttadd T₁ T₂) == ttadd (t₁ T₁) (t₁ T₂)
-- split (ttadd T₁ T₂) == ttadd (