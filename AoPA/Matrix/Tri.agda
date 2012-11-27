open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Product
open import Data.Sum

import Matrix.Abstract
import Matrix.NewNewSplit
open import Matrix.STree

open import Matrix.NonAssociativeNonRing

open import Level using () renaming (zero to Lzero)



module Matrix.Tri (NAR : NonAssociativeNonRing Lzero Lzero) where


open Matrix.Abstract (NAR)
open Matrix.NewNewSplit (NAR)



data Tri : Splitting → Set where
  one : Tri one
  two : ∀ {s₁ s₂} → Tri s₁ → SplitMat s₁ s₂ → 
                             Tri s₂ → 
                    Tri (deeper s₁ s₂)

T0 : ∀ {s} -> Tri s
T0 {one} = one
T0 {deeper y y'} = two T0 sZero T0

tvecmul : ∀ {s₁} -> Tri s₁ -> SplitVec s₁ -> SplitVec s₁
tvecmul {one} t v = one R0
tvecmul {deeper s₁ s₂} (two T₁ R T₂) (two v₁ v₂) = two (splitVecAdd (tvecmul T₁ v₁) (splitMatVecMul R v₂)) (tvecmul T₂ v₂)

vectmul : ∀ {s₁} -> SplitVec s₁ -> Tri s₁ -> SplitVec s₁
vectmul {one} t v = one R0
vectmul {deeper s₁ s₂} (two v₁ v₂) (two T₁ R T₂) = two (vectmul v₁ T₁) (splitVecAdd (splitVecMatMul v₁ R) (vectmul v₂ T₂))


_TS*_ : ∀ {s₁ s₂} -> Tri s₁ -> SplitMat s₁ s₂ -> SplitMat s₁ s₂
_TS*_ {one} {one} t r = Sing R0
_TS*_ {deeper y y'} {one} T (CVec v) = CVec (tvecmul T v)
_TS*_ {one} {deeper y y'} t r = RVec zeroVec
_TS*_ {deeper s₁ s₂} {deeper t₁ t₂} (two T₁ R T₂) (quad A₁ A₂ A₃ A₄) = quad (splitAdd (T₁ TS* A₁) (splitMul R A₃)) (splitAdd (T₁ TS* A₂) (splitMul R A₄)) (T₂ TS* A₃) (T₂ TS* A₄)

_ST*_ : ∀ {s₁ s₂} ->  SplitMat s₁ s₂ -> Tri s₂ -> SplitMat s₁ s₂
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



tri1 : ∀ {s₁ s₂} -> Tri (deeper s₁ s₂) -> Tri s₁
tri1 (two y y' y0) = y
tri2 : ∀ {s₁ s₂} -> Tri (deeper s₁ s₂) -> Tri s₂
tri2 (two y y' y0) = y0
rec : ∀ {s₁ s₂} -> Tri (deeper s₁ s₂) -> SplitMat s₁ s₂
rec (two y y' y0) = y'
split : ∀ {s₁ s₂} -> Tri (deeper s₁ s₂) -> Tri s₁ × SplitMat s₁ s₂ × Tri s₂
split = ⟨ tri1 , rec , tri2 ⟩

unsplit : ∀ {s₁ s₂} -> Tri s₁ × SplitMat s₁ s₂ × Tri s₂ -> Tri (deeper s₁ s₂)
unsplit (T₁ , R , T₂) = two T₁ R T₂


unsplit∘split≡id : ∀ {s₁ s₂} (t : Tri (deeper s₁ s₂)) -> unsplit ( split t) ≡ t
unsplit∘split≡id (two T₁ R T₂) = refl


-- the triangles are supposed to be transitively closed!
valiantOverlap : ∀ {s₁ s₂} -> Tri s₁ -> SplitMat s₁ s₂ -> Tri s₂ -> SplitMat s₁ s₂
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

foldTri : ∀ {b} {s : Splitting} {B : Splitting -> Set b} → (one' : B one) → (two' : ∀ {s₁ s₂} -> B s₁ -> SplitMat s₁ s₂ -> B s₂ -> B (deeper s₁ s₂) ) → Tri s → B s
foldTri one' two' one = one'
foldTri one' two' (two T₁ R T₂) = two' (foldTri one' two' T₁) R (foldTri one' two' T₂)


-- λ t₁ r t₂ -> two t₁ (valiantOverlap t₁ r t₂) t₂
valiantOverlap' : ∀ {s₁ s₂} -> Tri s₁ -> SplitMat s₁ s₂ -> Tri s₂ -> Tri (deeper s₁ s₂)
valiantOverlap' T₁ R T₂ = two T₁ (valiantOverlap T₁ R T₂) T₂

valiantFold : ∀ {s} → Tri s → Tri s
valiantFold = foldTri one valiantOverlap'


-- splitmat is fixed pt of F A = [R + Vec R + Vec R + A × A × A × A]
-- vo is fixedpt of 
-- 
-- X (two T₁ R T₂) = [ id , ? , ? , quad  ] 

-- X (two (T₁, R, T₂)) = 
-- X = 
-- input en ((T × A × T) × (A × A × A × A) × (T × A × T))
-- säg quad : A × A × A × A → SplitMat

-- now, properties: 

-- t₁ (ttadd T₁ T₂) == ttadd (t₁ T₁) (t₁ T₂)
-- split (ttadd T₁ T₂) == ttadd (