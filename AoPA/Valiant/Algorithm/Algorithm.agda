open import Valiant.Abstract.NonAssociativeNonRing
open import Valiant.Concrete.Splitting

module Valiant.Algorithm.Algorithm {l₁ l₂} (NAR : NonAssociativeNonRing l₁ l₂) where

import Valiant.Concrete.Tri as Tri
open Tri NAR
import Valiant.Concrete.Tri.Operations
open Valiant.Concrete.Tri.Operations NAR
import Valiant.Concrete.Mat.Operations
open Valiant.Concrete.Mat.Operations NAR
import Valiant.Concrete.Mat as Mat
open Mat NAR

-- the triangles are supposed to be transitively closed!
valiantOverlap : ∀ {s₁ s₂} -> Tri s₁ -> Mat s₁ s₂ -> Tri s₂ -> Mat s₁ s₂
valiantOverlap {one} {one} A' C B' = C
valiantOverlap {one} {deeper s₁ s₂} A' (RVec v) B' = RVec (v |◂ B')
valiantOverlap {deeper s₁ s₂} {one} A' (CVec v) B' = CVec (A' ◂| v)
valiantOverlap {deeper s₁ s₂} {deeper s₃ s₄} (two A₁ A₂ A₃) (quad C₂ C₄ C₁ C₃) (two B₃ B₂ B₁) = quad X₂ X₄ X₁ X₃
  where X₁ = valiantOverlap A₃ C₁ B₃
        X₂ = valiantOverlap A₁ (C₂ + (A₂ * X₁)) B₃
        X₃ = valiantOverlap A₃ (C₃ + (X₁ * B₂)) B₁
        X₄ = valiantOverlap A₁ (C₄ + ((A₂ * X₃) + (X₂ * B₂))) B₁

valiant : ∀ {s} -> Tri s -> Tri s
valiant one          = one
valiant (two A C B)  = two A' (valiantOverlap A' C B') B'
  where A' = (valiant A)
        B' = (valiant B)



valiantOverlap' : ∀ {s₁ s₂} -> Tri s₁ -> Mat s₁ s₂ -> Tri s₂ -> Tri (deeper s₁ s₂)
valiantOverlap' T₁ R T₂ = two T₁ (valiantOverlap T₁ R T₂) T₂

valiantFold : ∀ {s} → Tri s → Tri s
valiantFold = foldTri one valiantOverlap'
