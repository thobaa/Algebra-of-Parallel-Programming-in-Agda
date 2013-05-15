open import Valiant.Abstract.NonAssociativeNonRing
open import Valiant.Abstract.NonAssociativeNonRing.Structure using (IsNonAssociativeNonRing)

open import Valiant.Concrete.Splitting

open import Data.Product using (proj₁; proj₂; _×_; _,_)
import Relation.Binary.EqReasoning as EqR


module Valiant.Specs.Overlap {l₁ l₂} (NAR : NonAssociativeNonRing l₁ l₂) where




import Valiant.Concrete.Tri using (Tri; foldTri-intro; one; two)
import Valiant.Concrete.Tri.Operations
import Valiant.Concrete.Mat --using (Mat; Sing; RVec; CVec; quad; one; two)
import Valiant.Concrete.Mat.Operations
import Valiant.Concrete.Mat.Properties
import Valiant.Helper.Definitions
import Valiant.Algorithm.Algorithm
open Valiant.Concrete.Tri NAR
open Valiant.Concrete.Tri.Operations NAR
open Valiant.Concrete.Mat.Operations NAR
open Valiant.Concrete.Mat.Properties NAR
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

open import Level using (Level) renaming (zero to lzero; _⊔_ to _l⊔_; suc to lsuc)

open NonAssociativeNonRing NAR using (_≈_) renaming (isEquivalence to isEquivalenceR; +-commutativeMonoid to cmr; +-cong to R+-cong; zero to R-zero; +-identity to R+-identity; refl to ≈-refl)

private
  _←_   : ∀ {i j k : Level} → Set i → Set j → Set (lsuc k l⊔ i l⊔ j) --(lsuc lzero l⊔ (j l⊔ i))
_←_ {i} {j} {k} B A  =  B → A → Set k

-- rowspec: 
-- U⁺ R⁺ + R⁺ L⁺ + R = R⁺
-- 
rowSpec : ∀ {s} → Vec s ← (Vec s × Tri s)  
rowSpec v⁺ (v , T) = v⁺ |◂ T ⊕ v v≈ v⁺

colSpec : ∀ {s} → Vec s ← (Tri s × Vec s)
colSpec v⁺ (T , v) = T ◂| v⁺ ⊕ v v≈ v⁺ 

overlapRow-corr : ∀ {s} (v : Vec s) (T : Tri s) → rowSpec (overlapRow v T) (v , T)
overlapRow-corr (one x) one = one-eq (proj₁ R+-identity x) --lätt
overlapRow-corr {deeper s₁ s₂} (two u v) (two U R L) = two-eq (overlapRow-corr u U) (begin 
  (overlapRow u U |* R ⊕ overlapRow (overlapRow u U |* R ⊕ v) L |◂ L) ⊕ v 
    ≈⟨ ⊕-cong (commV (overlapRow u U |* R) (overlapRow (overlapRow u U |* R ⊕ v) L |◂ L)) v-refl ⟩
  (overlapRow (overlapRow u U |* R ⊕ v) L |◂ L ⊕ overlapRow u U |* R) ⊕ v
    ≈⟨ assocV (overlapRow (overlapRow u U |* R ⊕ v) L |◂ L) (overlapRow u U |* R) v ⟩
  overlapRow (overlapRow u U |* R ⊕ v) L |◂ L ⊕ (overlapRow u U |* R ⊕ v)
    ≈⟨ overlapRow-corr (overlapRow u U |* R ⊕ v) L ⟩
  overlapRow (overlapRow u U |* R ⊕ v) L ∎)
  where open EqR (record { Carrier = Vec s₂; _≈_ = _v≈_; isEquivalence = v-isEquivalence })


overlapCol-corr : ∀ {s} (T : Tri s) (v : Vec s) → colSpec (overlapCol T v) (T , v) 
overlapCol-corr one (one x) = one-eq (proj₁ R+-identity x)
overlapCol-corr {deeper s₁ s₂} (two U R L) (two u v) = two-eq pf1 (overlapCol-corr L v)
  where pf1 : (U ◂| overlapCol U (R *| overlapCol L v ⊕ u) ⊕ R *| overlapCol L v)
                ⊕ u
                v≈ overlapCol U (R *| overlapCol L v ⊕ u)
        pf1 = begin 
              (U ◂| overlapCol U (R *| overlapCol L v ⊕ u) ⊕ R *| overlapCol L v) ⊕ u 
                ≈⟨ assocV (U ◂| overlapCol U (R *| overlapCol L v ⊕ u)) (R *| overlapCol L v) u ⟩
              U ◂| overlapCol U (R *| overlapCol L v ⊕ u) ⊕ (R *| overlapCol L v ⊕ u)
                ≈⟨ overlapCol-corr U (R *| overlapCol L v ⊕ u) ⟩
              overlapCol U (R *| overlapCol L v ⊕ u) ∎
          where open EqR (record { Carrier = Vec s₁; _≈_ = _v≈_; isEquivalence = v-isEquivalence })





{-
valiant-row-correctness0 : ∀ {s₁ s₂} (u : Vec s₁) (v : Vec s₂) (U : Tri s₁) (R : Mat s₁ s₂) (L : Tri s₂) → (zeroVec ⊕
       (overlapRow u U |* R ⊕ extendRow (overlapRow u U) R L v |◂ L))
      ⊕ v
      v≈ extendRow (overlapRow u U) R L v
valiant-row-correctness0 (one x) (one y) one (Sing z) one = one-eq (begin 
  (R0 R+ (x R* z R+ R0)) R+ y 
    ≈⟨ R+-cong (proj₁ R+-identity (x R* z R+ R0)) ≈-refl ⟩ 
 (x R* z R+ R0) R+ y 
    ≈⟨ R+-cong (proj₂ R+-identity (x R* z)) ≈-refl ⟩ 
  x R* z R+ y ∎)
   where open EqR (record { Carrier = R; _≈_ = _≈_; isEquivalence = isEquivalenceR })
valiant-row-correctness0 (two u v) (one x) (two U R' L) (CVec (two u' v')) one = one-eq {!!} -- lätt
                         {-one-eq (begin 
                         (R0 R+ (two (overlapRow u U) (extendRow (overlapRow u U) R' L v) ∙ v' R+ R0)) R+ x 
                           ≈⟨ R+-cong (proj₁ R+-identity (two (overlapRow u U) (extendRow (overlapRow u U) R' L v) ∙ v' R+ R0)) ≈-refl ⟩ 
                         (two (overlapRow u U) (extendRow (overlapRow u U) R' L v) ∙ v' R+ R0) R+ x 
                           ≈⟨ R+-cong (proj₂ R+-identity (two (overlapRow u U) (extendRow (overlapRow u U) R' L v) ∙ v')) ≈-refl ⟩ 
                         two (overlapRow u U) (extendRow (overlapRow u U) R' L v) ∙ v' R+ x ∎)-}
   where open EqR (record { Carrier = R; _≈_ = _≈_; isEquivalence = isEquivalenceR })

valiant-row-correctness0 (one x) (two u' v) one (RVec (two u v')) (two U R' L) = two-eq pf1 pf2
  where pf1 : ∀ {s₁}{x : R}{u u' : Vec s₁}{U : Tri s₁} → (zeroVec ⊕ (x ⊛| u ⊕ extendRow (one x) (rVec u) U u' |◂ U)) ⊕ u'
                                                               v≈ 
                                                         extendRow (one x) (rVec u) U u' 
        pf1 {s₁}{x}{u}{u'}{U} = begin 
            (zeroVec ⊕ (x ⊛| u ⊕ extendRow (one x) (rVec u) U u' |◂ U)) ⊕ u' 
              ≈⟨ {!!} ⟩ 
            extendRow (one x) (rVec u) U u' ∎
          where open EqR (record { Carrier = Vec s₁; _≈_ = _v≈_; isEquivalence = isEquivalenceV})
        pf2 : (zeroVec ⊕ (x ⊛| v' ⊕ (extendRow (one x) (rVec u) U u' |* R' ⊕ extendRow (two (one x) (extendRow (one x) (rVec u) U u'))
                   (rVec v' over R') L v
                   |◂ L)))
                ⊕ v
                v≈
                extendRow (two (one x) (extendRow (one x) (rVec u) U u')) (rVec v' over R') L v 
        pf2 = {!!}
valiant-row-correctness0 (two u v') (two u' v) (two U R L) (quad A B C D) (two U' R' L') = two-eq pf1 pf2
  where pf1 : ∀ {s₁ s₂ s₁'} {u : Vec s₁} {u' : Vec s₁'} {U : Tri s₁} {U' : Tri s₁'} {R : Mat s₁ s₂} {L : Tri s₂} {v' : Vec s₂} {A : Mat s₁ s₁' } {C : Mat s₂ s₁'} → (zeroVec ⊕
                 ((overlapRow u U |* A ⊕ extendRow (overlapRow u U) R L v' |* C) ⊕
                  extendRow
                  (two (overlapRow u U)
                   (extendRow (overlapRow u U) R L v'))
                  (A over C) U' u'
                  |◂ U'))
                ⊕ u'
                v≈
                extendRow
                (two (overlapRow u U)
                 (extendRow (overlapRow u U) R L v'))
                (A over C) U' u'
        pf1 {s₁}{s₂}{s₁'} {u}{u'}{U}{U'}{R}{L}{v'}{A}{C}= begin 
            (zeroVec ⊕ ((overlapRow u U |* A ⊕ extendRow (overlapRow u U) R L v' |* C) ⊕ extendRow (two (overlapRow u U) (extendRow (overlapRow u U) R L v')) (A over C) U' u' |◂ U')) ⊕ u' 
                          ≈⟨ {!!} ⟩ 
            {!!}
                          ≈⟨ {!valiant-row-correctness0!} ⟩ 
            (extendRow (two (overlapRow u U) (extendRow (overlapRow u U) R L v')) (A over C) U' u' ∎)
          where open EqR (record { Carrier = Vec s₁'; _≈_ = _v≈_; isEquivalence = isEquivalenceV})
        pf2 : {!!}
        pf2 = {!!}

abstract 
 valiant-row-correctness1 : ∀ {s} (u : Vec s) (U : Tri s) → (zeroVec ⊕ overlapRow u U |◂ U) ⊕ u v≈ overlapRow u U
 valiant-row-correctness1 (one x) one = one-eq (begin 
                         (R0 R+ R0) R+ x 
                           ≈⟨ R+-cong (proj₁ R+-identity R0) ≈-refl ⟩
                         R0 R+ x 
                           ≈⟨ proj₁ R+-identity x ⟩
                         
                         x ∎)
   where open EqR (record { Carrier = R; _≈_ = _≈_; isEquivalence = isEquivalenceR })
 valiant-row-correctness1 (two u v) (two U R L) = two-eq (valiant-row-correctness1 u U) (valiant-row-correctness0 u v U R L)


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

-}