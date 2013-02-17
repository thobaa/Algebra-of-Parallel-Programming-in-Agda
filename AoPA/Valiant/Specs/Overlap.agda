open import Valiant.Abstract.NonAssociativeNonRing
open import Valiant.Abstract.NonAssociativeNonRing.Structure using (IsNonAssociativeNonRing)


open import Data.Product using (proj₁; proj₂)
import Relation.Binary.EqReasoning as EqR


module Valiant.Specs.Overlap {l₁ l₂} (NAR : NonAssociativeNonRing l₁ l₂) where



import Valiant.Concrete.Tri using (Tri; foldTri-intro; one; two)
import Valiant.Concrete.Tri.Operations
import Valiant.Concrete.Mat --using (Mat; Sing; RVec; CVec; quad; one; two)
import Valiant.Concrete.Mat.Operations
import Valiant.Helper.Definitions
import Valiant.Algorithm.Algorithm
open Valiant.Concrete.Tri NAR
open Valiant.Concrete.Tri.Operations NAR
open Valiant.Concrete.Mat.Operations NAR
open Valiant.Concrete.Mat NAR
open Valiant.Helper.Definitions NAR
open Valiant.Algorithm.Algorithm NAR

import Valiant.Concrete.Tri.Properties
import Valiant.Concrete.Tri.Equalities
import Valiant.Concrete.Tri.Congruences
import Valiant.Concrete.Tri.CommutativeMonoid

import Valiant.Concrete.Tri.Distributivities
open Valiant.Concrete.Tri.Properties NAR
open Valiant.Concrete.Tri.Equalities NAR
open Valiant.Concrete.Tri.Congruences NAR
open Valiant.Concrete.Tri.CommutativeMonoid NAR
open Valiant.Concrete.Tri.Distributivities NAR


open NonAssociativeNonRing NAR using (_≈_) renaming (isEquivalence to isEquivalenceR; +-commutativeMonoid to cmr; +-cong to R+-cong; zero to R-zero; +-identity to R+-identity; refl to ≈-refl)


valiant-row-correctness0 : ∀ {s₁ s₂} (u : Vec s₁) (v : Vec s₂) (U : Tri s₁) (R : Mat s₁ s₂) (L : Tri s₂) → (zeroVec ⊕
       (overlapRow u U |* R ⊕ extendRow (overlapRow u U) R L v |◂ L))
      ⊕ v
      v≈ extendRow (overlapRow u U) R L v
valiant-row-correctness0 (Valiant.Concrete.Mat.one x) (Valiant.Concrete.Mat.one y) Valiant.Concrete.Tri.one (Valiant.Concrete.Mat.Sing z) Valiant.Concrete.Tri.one = Valiant.Concrete.Tri.Equalities.one-eq (begin 
  (R0 R+ (x R* z R+ R0)) R+ y 
    ≈⟨ R+-cong (proj₁ R+-identity (x R* z R+ R0)) ≈-refl ⟩ 
 (x R* z R+ R0) R+ y 
    ≈⟨ R+-cong (proj₂ R+-identity (x R* z)) ≈-refl ⟩ 
  x R* z R+ y ∎)
   where open EqR (record { Carrier = R; _≈_ = _≈_; isEquivalence = isEquivalenceR })
valiant-row-correctness0 (Valiant.Concrete.Mat.two u v) (Valiant.Concrete.Mat.one x) (Valiant.Concrete.Tri.two U R' L) (Valiant.Concrete.Mat.CVec v') Valiant.Concrete.Tri.one = Valiant.Concrete.Tri.Equalities.one-eq (begin 
                         (R0 R+ (two (overlapRow u U) (extendRow (overlapRow u U) R' L v) ∙ v' R+ R0)) R+ x 
                           ≈⟨ R+-cong (proj₁ R+-identity (two (overlapRow u U) (extendRow (overlapRow u U) R' L v) ∙ v' R+ R0)) ≈-refl ⟩ 
                         (two (overlapRow u U) (extendRow (overlapRow u U) R' L v) ∙ v' R+ R0) R+ x 
                           ≈⟨ R+-cong (proj₂ R+-identity (two (overlapRow u U) (extendRow (overlapRow u U) R' L v) ∙ v')) ≈-refl ⟩ 
                         two (overlapRow u U) (extendRow (overlapRow u U) R' L v) ∙ v' R+ x ∎)
   where open EqR (record { Carrier = R; _≈_ = _≈_; isEquivalence = isEquivalenceR })

valiant-row-correctness0 (Valiant.Concrete.Mat.one x) (Valiant.Concrete.Mat.two u' v) Valiant.Concrete.Tri.one (Valiant.Concrete.Mat.RVec (Valiant.Concrete.Mat.two u v')) (Valiant.Concrete.Tri.two U R' L) = Valiant.Concrete.Tri.Equalities.two-eq pf1 {!begin ? ≈⟨ ? ⟩ ? ∎!}
  where pf1 : ∀ {s₁}{x : R}{u u' : Vec s₁}{U : Tri s₁} → (zeroVec ⊕ (x ⊛| u ⊕ extendRow (Valiant.Concrete.Mat.one x) (rVec u) U u' |◂ U)) ⊕ u'
                                                               v≈ 
                                                               extendRow (Valiant.Concrete.Mat.one x) (rVec u) U u' 
        pf1 {s₁}{x}{u}{u'}{U} = begin 
            (zeroVec ⊕ (x ⊛| u ⊕ extendRow (Valiant.Concrete.Mat.one x) (rVec u) U u' |◂ U)) ⊕ u' 
              ≈⟨ {!!} ⟩ 
            extendRow (Valiant.Concrete.Mat.one x) (rVec u) U u' ∎
          where open EqR (record { Carrier = Vec s₁; _≈_ = _v≈_; isEquivalence = isEquivalenceV})
        pf2 : {!!} 
        pf2 = {!!}
valiant-row-correctness0 (Valiant.Concrete.Mat.two u v') (Valiant.Concrete.Mat.two u' v) (Valiant.Concrete.Tri.two U R L) (Valiant.Concrete.Mat.quad A B C D) (Valiant.Concrete.Tri.two U' R' L') = Valiant.Concrete.Tri.Equalities.two-eq {!!} {!!}

abstract 
 valiant-row-correctness1 : ∀ {s} (u : Vec s) (U : Tri s) → (zeroVec ⊕ overlapRow u U |◂ U) ⊕ u v≈ overlapRow u U
 valiant-row-correctness1 (Valiant.Concrete.Mat.one x) Valiant.Concrete.Tri.one = Valiant.Concrete.Tri.Equalities.one-eq (begin 
                         (R0 R+ R0) R+ x 
                           ≈⟨ R+-cong (proj₁ R+-identity R0) ≈-refl ⟩
                         R0 R+ x 
                           ≈⟨ proj₁ R+-identity x ⟩
                         
                         x ∎)
   where open EqR (record { Carrier = R; _≈_ = _≈_; isEquivalence = isEquivalenceR })
 valiant-row-correctness1 (Valiant.Concrete.Mat.two u v) (Valiant.Concrete.Tri.two U R L) = Valiant.Concrete.Tri.Equalities.two-eq (valiant-row-correctness1 u U) (valiant-row-correctness0 u v U R L)


{-Goal: (zeroVec ⊕
       (overlapRow u U |* R ⊕ extendRow (overlapRow u U) R L v |◂ L))
      ⊕ v
      v≈ extendRow (overlapRow u U) R L v
————————————————————————————————————————————————————————————
L   : Tri s₂
R   : Mat s₁ s₂
U   : Tri s₁
v   : Vec s₂
u   : Vec s₁
s₂  : Splitting
s₁  : Splitting
NAR : NonAssociativeNonRing l₁ l₂
l₂  : Level
l₁  : Level-}

{-
Goal: ((U ◂| extendCol U R u (overlapCol L v) ⊕
        R *| overlapCol L v)
       ⊕ zeroVec)
      ⊕ u
      v≈ extendCol U R u (overlapCol L v)
————————————————————————————————————————————————————————————
v   : Vec .s₂
u   : Vec .s₁
L   : Tri .s₂
R   : Mat .s₁ .s₂
U   : Tri .s₁
.s₂ : Splitting
.s₁ : Splitting
NAR : NonAssociativeNonRing l₁ l₂
l₂  : Level
l₁  : Level

-}

{-
Goal: (L ◂| overlapCol L v ⊕ zeroVec) ⊕ v v≈ overlapCol L v
————————————————————————————————————————————————————————————
v   : Vec .s₂
u   : Vec .s₁
L   : Tri .s₂
R   : Mat .s₁ .s₂
U   : Tri .s₁
.s₂ : Splitting
.s₁ : Splitting
NAR : NonAssociativeNonRing l₁ l₂
l₂  : Level
l₁  : Level-}