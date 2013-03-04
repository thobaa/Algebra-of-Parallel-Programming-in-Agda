open import Valiant.Abstract.NonAssociativeNonRing
open import Valiant.Concrete.Splitting

module Valiant.Algorithm.Algorithm {l₁ l₂} (NAR : NonAssociativeNonRing l₁ l₂) where

import Valiant.Concrete.Tri
open Valiant.Concrete.Tri NAR
import Valiant.Concrete.Tri.Operations
open Valiant.Concrete.Tri.Operations NAR
import Valiant.Concrete.Mat.Operations
open Valiant.Concrete.Mat.Operations NAR
import Valiant.Concrete.Mat
open Valiant.Concrete.Mat NAR

-- accumulates the results in the first vector.
{-
3overlap : ∀ {s₁ s₂} → Vec s₁ → Vec s₂ → Tri (deeper s₁ s₂) → Vec (deeper s₁ s₂)
3overlap u v (Valiant.Concrete.Tri.two Valiant.Concrete.Tri.one R L) = {!!}
3overlap u v (Valiant.Concrete.Tri.two (Valiant.Concrete.Tri.two U R L) R' L') = {!!} 
-}

--3ov : ∀ {s₁ s₂} → Tri  → Vec s₁ → Vec s₂ → Tri (deeper s₁ s₂) → Vec (deeper s₁ s₂)

open NonAssociativeNonRing NAR renaming (_+_ to _R+_; _*_ to _R*_)

-- första vec klar.
extendRow : ∀ {s₁ s₂} → Vec s₁ → Mat s₁ s₂ → Tri s₂ → Vec s₂ → Vec s₂
extendRow {one} {one} (one x) (Sing y) L (one z) = one (x R* y R+ z)
extendRow {deeper s₁ s₂} {one} (two u v) (CVec (two u' v')) L (one x) = Valiant.Concrete.Mat.one ((u ∙ u') R+ (v ∙ v') R+ x) --u⁺ |* R ⊕ v
extendRow u⁺ R' (two U R L) (two u v) = two u' v'
  where u' = extendRow u⁺ (left R') U u
        v' = extendRow (two u⁺ u') (right R' over R) L v

overlapRow : ∀ {s} → Vec s → Tri s → Vec s
overlapRow (one x) one = one x
overlapRow (two u v) (two U R L) = two u⁺ v⁺
  where u⁺ = overlapRow u U -- sedan ska denna extendas till v
        v⁺ = overlapRow (u⁺ |* R ⊕ v) L --extendRow u' R L v


-- these work from down and up!

-- we want that the rows of R are split as U. the cols of R should be split as 
-- u, to allow  
extendCol : ∀ {s₁ s₂} → Tri s₁ → Mat s₁ s₂ → Vec s₁ → Vec s₂ → Vec s₁
extendCol {one} {s₂} U R u v⁺ = R *| v⁺ ⊕ u
extendCol (two U R L) R' (two u v) v⁺ = two u'' v''
  where v'' = extendCol L (lower R') v v⁺ -- saknas det inte något här?
        u'' = extendCol U (R M++ upper R') u (two v'' v⁺)

-- U R⁺ + R = R⁺  , R = (u v)', R⁺ = (u⁺ v⁺)'
-- U = A B
--       C
-- A B |u⁺| = |A u⁺ + B v⁺| 
--   C |v⁺|   |C v⁺       |
-- så: 
-- A u⁺ + B v⁺ + u = u⁺
-- C v⁺ +        v = v⁺
overlapCol : ∀ {s} → Tri s → Vec s → Vec s
overlapCol one (one x) = one x
overlapCol (two U R L) (two u v) = two u⁺ v⁺
  where v⁺ = overlapCol L v
        u⁺ = overlapCol U (R *| v⁺ ⊕ u) --extendCol U R u v'
        

-- the triangles are supposed to be transitively closed!
valiantOverlap : ∀ {s₁ s₂} -> Tri s₁ -> Mat s₁ s₂ -> Tri s₂ -> Mat s₁ s₂
valiantOverlap {one} {one} one C one = C
valiantOverlap {one} {deeper s₁ s₂} one (RVec v) L = Valiant.Concrete.Mat.RVec (overlapRow v L) --u' M++ v'
--  where u' = valiantOverlap one (rVec u) U
--        v' = valiantOverlap {!two!} (rVec v) {!!} -- går ej, för höjden ska vara ett.

valiantOverlap {deeper s₁ s₂} {one} U (CVec v) one = Valiant.Concrete.Mat.CVec (overlapCol U v) --A' ◂* v + v
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
