open import Data.Nat
open import Data.Fin using (Fin; fromℕ; fromℕ≤; toℕ;  raise; reduce≥) 
                     renaming (zero to f0; suc to fsuc)

open import Valiant.Abstract.NonAssociativeNonRing
open import Valiant.Concrete.Splitting
module Valiant.Representation.MatRep {l₁ l₂} (NAR : NonAssociativeNonRing l₁ l₂) where

import Valiant.Helper.Definitions
import Valiant.Concrete.Mat
import Valiant.Abstract.Matrix

open Valiant.Helper.Definitions NAR
open Valiant.Concrete.Mat NAR
open Valiant.Abstract.Matrix NAR

-- vector stuff
projVec : ∀ {s} → Vec s → Vector (splitSize s)
projVec (one x) = λ i → x
projVec (two y y') = V++ (projVec y) (projVec y')

projVec' : ∀ {m} → Vec (simpleSplit m) → Vector (suc m)
projVec' {zero} (one x) = λ i → x
projVec' {suc n} (two v₁  v₂) = V++ (projVec' v₁) (projVec' v₂)

vecToRMat : ∀ {n} → Vector n → Matrix 1 n
vecToRMat v = λ i j → v j

vecToCMat : ∀ {n} → Vector n → Matrix n 1
vecToCMat v = λ i j → v i

embedVec : ∀ {n} → Vector (suc n) → Vec (simpleSplit n)
embedVec {zero} v = one (v f0)
embedVec {suc n} v = two (one (v f0)) (embedVec (λ x → v (fsuc x)))


-- the way we have it is: matToSplit: tar en matris till en konkret.
-- typ lista -> tree, den viktika delen är att vilket träd som helst kan formas
-- om till en lista. inte så viktigt att 
-- 

splitToMat : ∀ {s₁ s₂} → Mat s₁ s₂ → Matrix (splitSize s₁) (splitSize s₂)
{-splitToMat {zero} {zero} (Sing x) = λ i j → x
splitToMat {suc n} {zero} (CVec y) = {!!}
splitToMat {zero} {suc n} (RVec y) = {!!}
splitToMat {suc n} {suc n'} (quad A B 
                                  C D) = Four (splitToMat A) (splitToMat B) 
                                              (splitToMat C) (splitToMat D)
-}
splitToMat {one} {one} (Sing x) = λ _ _ → x 
splitToMat {deeper y y'} {one} (CVec y0) = vecToCMat (projVec y0)
splitToMat {one} {deeper y y'} (RVec y0) = vecToRMat (projVec y0)
splitToMat {deeper y y'} {deeper y0 y1} (quad A B 
                                                C D) = Four (splitToMat A) (splitToMat B) 
                                                            (splitToMat C) (splitToMat D)


-- should not be this way.???
-- nej. vi har inte en metod som skapar element av godtyckliga splittar.
--matToSplit : ∀ {s₁ s₂} → Matrix (splitSize s₁) (splitSize s₂) → Mat s₁ s₂
--matToSplit = {!!}

-- behöver en relation mellan alla 
-- splitToMat : ∀ {m n} → Mat 


-- i matrepproofs finns satsen vi vill ha.
{-
matToSplit {zero} {zero} mat = Sing (mat f0 f0)
matToSplit {suc n} {zero} mat = CVec (embedVec (λ x → mat x f0))
matToSplit {zero} {suc n} mat = RVec (embedVec (λ x → mat f0 x))
matToSplit {suc zero} {suc zero} mat = quad (Sing (mat f0 f0)) (Sing (mat f0 f1)) 
                                              (Sing (mat f1 f0)) (Sing (mat f1 f1))
matToSplit {suc zero} {suc (suc n)} mat = quad (Sing (mat f0 f0)) (RVec (embedVec (λ x → mat f0 (fsuc x)))) (Sing (mat f1 f0)) (RVec (embedVec (λ x → mat f1 (fsuc x))))
matToSplit {suc (suc n)} {suc zero} mat = quad (Sing (mat f0 f0)) (Sing (mat f0 f1)) (CVec (embedVec (λ x → mat (fsuc x) f0))) (CVec (embedVec (λ x → mat (fsuc x) f1)))
matToSplit {suc (suc n)} {suc (suc n')} mat = quad (Sing (mat f0 f0)) (RVec (embedVec (λ x → mat f0 (fsuc x)))) (CVec (embedVec (λ x → mat (fsuc x) f0))) (matToSplit (λ x x' → mat (fsuc x) (fsuc x')))
-}