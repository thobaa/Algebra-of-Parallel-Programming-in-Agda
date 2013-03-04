open import Valiant.Abstract.NonAssociativeNonRing
open import Valiant.Abstract.NonAssociativeNonRing.Structure using (IsNonAssociativeNonRing)
open import Algebra

open import Data.Product using (proj₁; proj₂)
open import Data.Unit using ()
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym)

import Relation.Binary.EqReasoning as EqR


open import Level using (Level) renaming (zero to lzero; _⊔_ to _l⊔_; suc to lsuc)

open import Valiant.Concrete.Splitting

module Valiant.Specs.JPSpec {l₁ l₂} (NAR : NonAssociativeNonRing l₁ l₂) where

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


import Valiant.Specs.Overlap
open Valiant.Specs.Overlap NAR
-- spec is: 
-- TC C = TC C * C + TC C

-- want at function satisfying the above

-- a relation from tris to tris.

-- example:
--∈ : {A : Set} → A ← ℙ A 
--∈ a s = s a 

{-
-- specification: XC + C = X, X ≥ C; JP Spec is actually X ≥ C and X ∙ X + X = X
-- which is probably not (quite) enough
JPTC : ∀ {s} → Tri s ← Tri s
JPTC C X = X ◂ C ◂+ C ≡ X

-- this should not be here. but where? In NAR? below stuff should be in their respective "operations" files, probably
postulate 
  _≤R_ : R ← R

_≤vec_ : ∀ {s} → Vec s ← Vec s
one x ≤vec one y = x ≤R y
two x₁ x₂ ≤vec two y₁ y₂ = x₁ ≤vec y₁ × x₂ ≤vec y₂

_≤■_ : ∀ {s₁ s₂} → Mat s₁ s₂ ← Mat s₁ s₂
Sing x ≤■ Sing y = x ≤R y
RVec u ≤■ RVec v = u ≤vec v
CVec u ≤■ CVec v = u ≤vec v
quad A₁ B₁ C₁ D₁ ≤■ quad A₂ B₂ C₂ D₂ = A₁ ≤■ A₂ × B₁ ≤■ B₂ × C₁ ≤■ C₂ × D₁ ≤■ D₂

_≤◂_ : ∀ {s} → Tri s ← Tri s
one ≤◂ one = ⊤
two U₁ R₁ L₁ ≤◂ two U₂ R₂ L₂ = U₁ ≤◂ U₂ × R₁ ≤■ R₂ × L₁ ≤◂ L₂

JPTC2 : ∀ {s} → Tri s ← Tri s
JPTC2 C X = C ≤◂ X


-- derivation
valiant-der : ∀ {s} → ∃ (λ f → JPTC {s} ⊒ fun f)
valiant-der = ({!!} , {!!})

-}

open NonAssociativeNonRing NAR using (_≈_) renaming (isEquivalence to isEquivalenceR; +-commutativeMonoid to cmr; +-cong to R+-cong; zero to R-zero; +-identity to R+-identity; refl to ≈-refl)

_←_   : ∀ {i j k : Level} → Set i → Set j → Set (lsuc k l⊔ i l⊔ j) --(lsuc lzero l⊔ (j l⊔ i))
_←_ {i} {j} {k} B A  =  B → A → Set k


-- different spec:
TC : ∀ {s} → Tri s ← Tri s
TC C X = X ◂ X ◂+ C t≈ X
-- TODO: perhaps replace ◂ with ▴ 

-- spec for rectangle
SubTC : ∀ {s₁ s₂} → Tri (deeper s₁ s₂) ← Mat s₁ s₂
SubTC (two U R L) X = (U ◂* X + X *◂ L) + R m≈ X

-- give name to valiant eq
φ : ∀ {s} → Tri s → Tri s
φ X = valiantFold X ◂ valiantFold X ◂+ X

-- these two are not very important.
-- ska det vara ≡ ? eller extension av ringolikhet
lemma-mul : ∀ {s₁ s₂} (U₁ U₂ : Tri s₁) (R₁ R₂ : Mat s₁ s₂) (L₁ L₂ : Tri s₂)  → 
  two U₁ R₁ L₁ ◂ two U₂ R₂ L₂ ≡ two (U₁ ◂ U₂) (U₁ ◂* R₂ + R₁ *◂ L₂) (L₁ ◂ L₂)
lemma-mul U₁ U₂ R₁ R₂ L₁ L₂ = refl

lemma-plus : ∀ {s₁ s₂} (U₁ U₂ : Tri s₁) (R₁ R₂ : Mat s₁ s₂) (L₁ L₂ : Tri s₂) → 
  two U₁ R₁ L₁ ◂+ two U₂ R₂ L₂ ≡ two (U₁ ◂+ U₂) (R₁ + R₂) (L₁ ◂+ L₂)
lemma-plus U₁ U₂ R₁ R₂ L₁ L₂ = refl

-- this is specifying equation for rectangle:
{-lemma-rect : ∀ {
  ((valiantFold T₁ ◂* valiantOverlap (valiantFold T₁) R (valiantFold T₂)
          +
          valiantOverlap (valiantFold T₁) R (valiantFold T₂) *◂ valiantFold T₂)
          + R)
-}

-- valiantOverlap satisfies the SubTC:
-- this is an important part of the proof!
-- 


-- proof that U * (ol U R L) + (ol U R L) * L + R = (ol U R L),                                   (U ◂* X + X *◂ L) + R m≈ X
-- We seem to need that U and L are transitively closed.

--valiant-row-correctness1 : ∀ {s} → (u : Vec s) (U : Tri s) → (zeroVec ⊕ overlapRow u U |◂ U) ⊕ u v≈ overlapRow u U 
--valiant-row-correctness1 = {!!}


valiant-sub-correctness : ∀ {s₁ s₂} (U : Tri s₁) (R : Mat s₁ s₂) (L : Tri s₂) → SubTC (two U R L) (valiantOverlap U R L)
valiant-sub-correctness one (Sing x) one = Valiant.Concrete.Tri.Equalities.Sing-eq (begin 
   (R0 R+ R0) R+ x 
     ≈⟨ R+-cong (proj₁ R+-identity R0) ≈-refl ⟩ 
   R0 R+ x 
     ≈⟨ proj₁ R+-identity x ⟩
   x ∎)
  where open EqR (record { Carrier = R; _≈_ = _≈_; isEquivalence = isEquivalenceR })
valiant-sub-correctness {one} {deeper s₁ s₂} one (RVec (two u v)) (two U R L) = RVec-eq (Valiant.Concrete.Tri.Equalities.two-eq pf1 pf2) -- vi behöver att a är tc, a = a + a*a
  where pf1 : (zeroVec ⊕ overlapRow u U |◂ U) ⊕ u v≈ overlapRow u U
        pf1 = begin 
            (zeroVec ⊕ overlapRow u U |◂ U) ⊕ u
              ≈⟨ assocV zeroVec (overlapRow u U |◂ U) u ⟩ 
            zeroVec ⊕ (overlapRow u U |◂ U ⊕ u)
              ≈⟨ identityˡV (overlapRow u U |◂ U ⊕ u) ⟩ 
            overlapRow u U |◂ U ⊕ u
              ≈⟨ overlapRow-corr u U ⟩ 
            (overlapRow u U ∎)
          where open EqR (record { Carrier = Vec s₁; _≈_ = _v≈_; isEquivalence = isEquivalenceV }) 
        pf2 : (zeroVec ⊕
                 (overlapRow u U |* R ⊕
                  overlapRow (overlapRow u U |* R ⊕ v) L |◂ L))
                ⊕ v
                v≈ overlapRow (overlapRow u U |* R ⊕ v) L
        pf2 = begin 
            (zeroVec ⊕ (overlapRow u U |* R ⊕ overlapRow (overlapRow u U |* R ⊕ v) L |◂ L)) ⊕ v
              ≈⟨ ⊕-cong (identityˡV (overlapRow u U |* R ⊕ overlapRow (overlapRow u U |* R ⊕ v) L |◂ L)) reflV ⟩
            ((overlapRow u U |* R ⊕
                overlapRow (overlapRow u U |* R ⊕ v) L |◂ L))
              ⊕ v
              ≈⟨ ⊕-cong (commV (overlapRow u U |* R) (overlapRow (overlapRow u U |* R ⊕ v) L |◂ L)) reflV ⟩
            (overlapRow (overlapRow u U |* R ⊕ v) L |◂ L ⊕ overlapRow u U |* R) ⊕ v

              ≈⟨ assocV (overlapRow (overlapRow u U |* R ⊕ v) L |◂ L) (overlapRow u U |* R) v ⟩
            overlapRow (overlapRow u U |* R ⊕ v) L |◂ L ⊕ (overlapRow u U |* R ⊕ v)
              ≈⟨ overlapRow-corr (overlapRow u U |* R ⊕ v) L ⟩ 
            overlapRow (overlapRow u U |* R ⊕ v) L ∎
          where open EqR (record { Carrier = Vec s₂; _≈_ = _v≈_; isEquivalence = isEquivalenceV }) 
valiant-sub-correctness {deeper s₁ s₂} {one} (Valiant.Concrete.Tri.two U R L) (CVec (two u v)) Valiant.Concrete.Tri.one = Valiant.Concrete.Tri.Equalities.CVec-eq (Valiant.Concrete.Tri.Equalities.two-eq pf1 pf2)
  where pf1 : ((U ◂| overlapCol U (R *| overlapCol L v ⊕ u) ⊕
                  R *| overlapCol L v)
                 ⊕ zeroVec)
                ⊕ u
                v≈ overlapCol U (R *| overlapCol L v ⊕ u) 
        pf1 = begin 
            ((U ◂| overlapCol U (R *| overlapCol L v ⊕ u) ⊕
                R *| overlapCol L v)
               ⊕ zeroVec)
              ⊕ u 
              ≈⟨ ⊕-cong (proj₂ identity (U ◂| overlapCol U (R *| overlapCol L v ⊕ u) ⊕ R *| overlapCol L v)) reflV ⟩ 
            ((U ◂| overlapCol U (R *| overlapCol L v ⊕ u) ⊕
                R *| overlapCol L v))
              ⊕ u 
              ≈⟨ assocV (U ◂| overlapCol U (R *| overlapCol L v ⊕ u)) (R *| overlapCol L v) u ⟩ 
            U ◂| overlapCol U (R *| overlapCol L v ⊕ u) ⊕
              (R *| overlapCol L v ⊕ u)
              ≈⟨ overlapCol-corr U (R *| overlapCol L v ⊕ u) ⟩ 
            overlapCol U (R *| overlapCol L v ⊕ u) ∎
          where open EqR (record { Carrier = Vec s₁; _≈_ = _v≈_; isEquivalence = isEquivalenceV })
                open CommutativeMonoid (record {
                                          Carrier = Vec s₁;
                                          _≈_ = _v≈_;
                                          _∙_ = _⊕_;
                                          ε = zeroVec;
                                          isCommutativeMonoid = isCommutativeMonoidV })
        pf2 : (L ◂| overlapCol L v ⊕ zeroVec) ⊕ v v≈ overlapCol L v 
        pf2 = begin 
            (L ◂| overlapCol L v ⊕ zeroVec) ⊕ v 
              ≈⟨ ⊕-cong (proj₂ identity (L ◂| overlapCol L v)) reflV ⟩
            L ◂| overlapCol L v ⊕ v
              ≈⟨ overlapCol-corr L v ⟩ 
            overlapCol L v ∎
          where open EqR (record { Carrier = Vec s₂; _≈_ = _v≈_; isEquivalence = isEquivalenceV })
                open CommutativeMonoid (record {
                                          Carrier = Vec s₂;
                                          _≈_ = _v≈_;
                                          _∙_ = _⊕_;
                                          ε = zeroVec;
                                          isCommutativeMonoid = isCommutativeMonoidV })
valiant-sub-correctness {deeper s₁ s₂} {deeper s₁' s₂'} (Valiant.Concrete.Tri.two U R L) (quad A B C D) (Valiant.Concrete.Tri.two U' R' L') = Valiant.Concrete.Tri.Equalities.quad-eq pfA pfB (valiant-sub-correctness L C U') pfD
  where pfC : (L ◂* valiantOverlap L C U' + valiantOverlap L C U' *◂ U') + C 
                m≈
              valiantOverlap L C U' 
        pfC = (valiant-sub-correctness L C U' )
        pfA : ∀ {s₁ s₂ s₁'} → {u : Tri s₁} {u' : Tri s₁'} {r : Mat s₁ s₂} {l : Tri s₂} {a : Mat s₁ s₁'} {c : Mat s₂ s₁'} → 
              ((u ◂* valiantOverlap u (a + r * valiantOverlap l c u') u' + r * valiantOverlap l c u') + valiantOverlap u (a + r * valiantOverlap l c u') u' *◂ u') + a
                m≈ 
              valiantOverlap u (a + r * valiantOverlap l c u') u'
        pfA {s₁} {s₂} {s₁'} {u} {u'} {r} {l} {a} {c} = begin 
              ((u ◂* valiantOverlap u (a + r * valiantOverlap l c u') u' + r * valiantOverlap l c u') + valiantOverlap u (a + r * valiantOverlap l c u') u' *◂ u') + a 
                ≈⟨ +-cong (assocM (u ◂* valiantOverlap u (a + r * valiantOverlap l c u') u') (r * valiantOverlap l c u') (valiantOverlap u (a + r * valiantOverlap l c u') u' *◂ u')) reflM ⟩
              (u ◂* valiantOverlap u (a + r * valiantOverlap l c u') u' + (r * valiantOverlap l c u' + valiantOverlap u (a + r * valiantOverlap l c u') u' *◂ u')) + a 
                ≈⟨ +-cong (+-cong reflM (commM (r * valiantOverlap l c u') (valiantOverlap u (a + r * valiantOverlap l c u') u' *◂ u'))) reflM ⟩       
              (u ◂* valiantOverlap u (a + r * valiantOverlap l c u') u' + (valiantOverlap u (a + r * valiantOverlap l c u') u' *◂ u' + r * valiantOverlap l c u')) + a 
                ≈⟨ +-cong (symM (assocM (u ◂* valiantOverlap u (a + r * valiantOverlap l c u') u') (valiantOverlap u (a + r * valiantOverlap l c u') u' *◂ u') (r * valiantOverlap l c u'))) reflM ⟩
              ((u ◂* valiantOverlap u (a + r * valiantOverlap l c u') u' + valiantOverlap u (a + r * valiantOverlap l c u') u' *◂ u') + r * valiantOverlap l c u') + a 
                ≈⟨ assocM (u ◂* valiantOverlap u (a + r * valiantOverlap l c u') u' +
                             valiantOverlap u (a + r * valiantOverlap l c u') u' *◂ u') (r * valiantOverlap l c u') a ⟩
              (u ◂* valiantOverlap u (a + r * valiantOverlap l c u') u' + valiantOverlap u (a + r * valiantOverlap l c u') u' *◂ u') + (r * valiantOverlap l c u' + a) 
                ≈⟨ +-cong reflM (commM (r * valiantOverlap l c u') a) ⟩
              (u ◂* valiantOverlap u (a + r * valiantOverlap l c u') u' + valiantOverlap u (a + r * valiantOverlap l c u') u' *◂ u') + (a + r * valiantOverlap l c u')
                ≈⟨ valiant-sub-correctness u (a + r * valiantOverlap l c u') u' ⟩
              valiantOverlap u (a + r * valiantOverlap l c u') u' ∎
            where open EqR (record { Carrier = Mat s₁ s₁'; _≈_ = _m≈_; isEquivalence = isEquivalenceM})
        pfD : ∀ {s₂ s₁' s₂'} {l : Tri s₂}{u' : Tri s₁'}{l' : Tri s₂'}{c : Mat s₂ s₁'} {d : Mat s₂ s₂'} {r' : Mat s₁' s₂'} → 
                (l ◂* valiantOverlap l (d + valiantOverlap l c u' * r') l' + (valiantOverlap l c u' * r' + valiantOverlap l (d + valiantOverlap l c u' * r') l' *◂ l')) + d
                  m≈ 
                valiantOverlap l (d + valiantOverlap l c u' * r') l'
        pfD {s₂} {s₁'} {s₂'} {l} {u'} {l'} {c} {d} {r'} = begin 
            (l ◂* valiantOverlap l (d + valiantOverlap l c u' * r') l' + (valiantOverlap l c u' * r' + valiantOverlap l (d + valiantOverlap l c u' * r') l' *◂ l')) + d 
              ≈⟨ +-cong (+-cong reflM (commM (valiantOverlap l c u' * r') (valiantOverlap l (d + valiantOverlap l c u' * r') l' *◂ l'))) reflM ⟩ 
            (l ◂* valiantOverlap l (d + valiantOverlap l c u' * r') l' + (valiantOverlap l (d + valiantOverlap l c u' * r') l' *◂ l' + valiantOverlap l c u' * r')) + d 
              ≈⟨ +-cong (symM (assocM (l ◂* valiantOverlap l (d + valiantOverlap l c u' * r') l') (valiantOverlap l (d + valiantOverlap l c u' * r') l' *◂ l') (valiantOverlap l c u' * r'))) reflM ⟩ 
            ((l ◂* valiantOverlap l (d + valiantOverlap l c u' * r') l' + valiantOverlap l (d + valiantOverlap l c u' * r') l' *◂ l') + valiantOverlap l c u' * r') + d 
              ≈⟨ assocM (l ◂* valiantOverlap l (d + valiantOverlap l c u' * r') l' + valiantOverlap l (d + valiantOverlap l c u' * r') l' *◂ l') (valiantOverlap l c u' * r') d ⟩ 
            (l ◂* valiantOverlap l (d + valiantOverlap l c u' * r') l' + valiantOverlap l (d + valiantOverlap l c u' * r') l' *◂ l') + (valiantOverlap l c u' * r' + d) 
              ≈⟨ +-cong reflM (commM (valiantOverlap l c u' * r') d) ⟩ 
            (l ◂* valiantOverlap l (d + valiantOverlap l c u' * r') l' + valiantOverlap l (d + valiantOverlap l c u' * r') l' *◂ l') + (d + valiantOverlap l c u' * r')
              ≈⟨ valiant-sub-correctness l (d + valiantOverlap l c u' * r') l' ⟩ 
            valiantOverlap l (d + valiantOverlap l c u' * r') l' ∎
            where open EqR (record { Carrier = Mat s₂ s₂' ; _≈_ = _m≈_; isEquivalence = isEquivalenceM})

        pfB : ∀ {s₁ s₂ s₁' s₂'} {u : Tri s₁} {r : Mat s₁ s₂} {l : Tri s₂} {a : Mat s₁ s₁'} {b : Mat s₁ s₂'} {c : Mat s₂ s₁'} {d : Mat s₂ s₂'} {u' : Tri s₁'} {r' : Mat s₁' s₂'} {l' : Tri s₂'} → ((u ◂* valiantOverlap u (b + (r * valiantOverlap l (d + valiantOverlap l c u' * r') l' + valiantOverlap u (a + r * valiantOverlap l c u') u' * r')) l' + r * valiantOverlap l (d + valiantOverlap l c u' * r') l') + (valiantOverlap u (a + r * valiantOverlap l c u') u' * r' + valiantOverlap u (b + (r * valiantOverlap l (d + valiantOverlap l c u' * r') l' + valiantOverlap u (a + r * valiantOverlap l c u') u' * r')) l' *◂ l')) + b
                m≈
              valiantOverlap u (b + (r * valiantOverlap l (d + valiantOverlap l c u' * r') l' + valiantOverlap u (a + r * valiantOverlap l c u') u' * r')) l'
        pfB {s₁} {s₂} {s₁'} {s₂'} {u} {r} {l} {a} {b} {c} {d} {u'} {r'} {l'}= begin 
            ((u ◂* valiantOverlap u (b + (r * valiantOverlap l (d + valiantOverlap l c u' * r') l' + valiantOverlap u (a + r * valiantOverlap l c u') u' * r')) l' 
                + -- lika dit
              r * valiantOverlap l (d + valiantOverlap l c u' * r') l') 
              + 
              (valiantOverlap u (a + r * valiantOverlap l c u') u' * r'
                +             
               valiantOverlap u (b + (r * valiantOverlap l (d + valiantOverlap l c u' * r') l' + valiantOverlap u (a + r * valiantOverlap l c u') u' * r')) l' *◂ l')) 
            + 
            b
              ≡⟨ refl ⟩
            ((T₁ + T₂) + (T₃ + T₄)) + T₅
              ≈⟨ +-cong (+-cong reflM (commM T₃ T₄)) reflM ⟩
            ((T₁ + T₂) + (T₄ + T₃)) + T₅
              ≈⟨ +-cong (symM (assocM (T₁ + T₂) T₄ T₃)) reflM ⟩
            (((T₁ + T₂) + T₄) + T₃) + T₅
              ≈⟨ +-cong (+-cong (assocM T₁ T₂ T₄) reflM) reflM ⟩
            ((T₁ + (T₂ + T₄)) + T₃) + T₅
              ≈⟨ +-cong (+-cong (+-cong reflM (commM T₂ T₄)) reflM) reflM ⟩
            ((T₁ + (T₄ + T₂)) + T₃) + T₅
              ≈⟨ +-cong (+-cong (symM (assocM T₁ T₄ T₂)) reflM) reflM ⟩
            (((T₁ + T₄) + T₂) + T₃) + T₅
              ≈⟨ +-cong (assocM (T₁ + T₄) T₂ T₃) reflM ⟩
            ((T₁ + T₄) + (T₂ + T₃)) + T₅
              ≈⟨ assocM (T₁ + T₄) (T₂ + T₃) T₅ ⟩
            (T₁ + T₄) + ((T₂ + T₃) + T₅)
              ≈⟨ +-cong reflM (commM (T₂ + T₃) T₅) ⟩
            (T₁ + T₄) + (T₅ + (T₂ + T₃))
              ≡⟨ refl ⟩
            (u ◂* valiantOverlap u (b + (r * valiantOverlap l (d + valiantOverlap l c u' * r') l' + valiantOverlap u (a + r * valiantOverlap l c u') u' * r')) l' 
              + 
             valiantOverlap u (b + (r * valiantOverlap l (d + valiantOverlap l c u' * r') l' + valiantOverlap u (a + r * valiantOverlap l c u') u' * r')) l' *◂ l') 
            + 
            (b 
              + 
             (r * valiantOverlap l (d + valiantOverlap l c u' * r') l' 
               + 
              valiantOverlap u (a + r * valiantOverlap l c u') u' * r'))
              ≈⟨ valiant-sub-correctness u (b + (r * valiantOverlap l (d + valiantOverlap l c u' * r') l' + valiantOverlap u (a + r * valiantOverlap l c u') u' * r')) l' ⟩ 
            valiantOverlap u (b + (r * valiantOverlap l (d + valiantOverlap l c u' * r') l' + valiantOverlap u (a + r * valiantOverlap l c u') u' * r'))
              l' ∎
            where open EqR (record { Carrier = Mat s₁ s₂' ; _≈_ = _m≈_; isEquivalence = isEquivalenceM})
                  T₁ : Mat s₁ s₂'
                  T₁ = u ◂*
                         valiantOverlap u
                         (b +
                          (r * valiantOverlap l (d + valiantOverlap l c u' * r') l' +
                           valiantOverlap u (a + r * valiantOverlap l c u') u' * r'))
                         l'
                  T₂ : Mat s₁ s₂'
                  T₂ = r * valiantOverlap l (d + valiantOverlap l c u' * r') l'
                  T₃ : Mat s₁ s₂'
                  T₃ = valiantOverlap u (a + r * valiantOverlap l c u') u' * r'
                  T₄ : Mat s₁ s₂'
                  T₄ = valiantOverlap u
                         (b +
                          (r * valiantOverlap l (d + valiantOverlap l c u' * r') l' +
                           valiantOverlap u (a + r * valiantOverlap l c u') u' * r'))
                         l'
                         *◂ l'
                  T₅ : Mat s₁ s₂'
                  T₅ = b
--((U ◂* valiantOverlap U (A + R * valiantOverlap L C U') U' +
--        R * valiantOverlap L C U')
--       + valiantOverlap U (A + R * valiantOverlap L C U') U' *◂ U')
--      + A
--      m≈ valiantOverlap U (A + R * valiantOverlap L C U') U'

--congTM : ∀ {s₁ s₂} {a b} {A : Set a} {B : Set b}
--       (f : Mat s₁ s₂ → Tri (deeper s₁ s₂)) {x y} → x m≈ y → f x t≈ f y
--congTM f pf = {!!}
abstract
 congT : ∀ {s₁ s₂} → {U U' : Tri s₁}{R R' : Mat s₁ s₂}{L L' : Tri s₂} → U t≈ U' → R m≈ R' → L t≈ L' → two U R L t≈ two U' R' L'
 congT = two-eq
 sub-correct : {s₁ s₂ : Splitting} → (U : Tri s₁) → (R : Mat s₁ s₂) → (L : Tri s₂) → two U ((U ◂* (valiantOverlap U R L) + (valiantOverlap U R L) *◂ L) + R) L t≈ two U (valiantOverlap U R L) L 
 sub-correct U R L = congT reflT (valiant-sub-correctness U R L) reflT
  --where open EqR isEquivalenceM renaming (cong to congM) 

-- TODO: my (Patrik's) intuition is that this lemma should be
-- subdivided to have a "non-recursive" φ

-- TODO: JPB: I would first solve valiant-corretness with explicit
-- recursion, then try to refactor into using a recursion operator
-- later.



-- kan man introducera "congT: om t1 t= t2 => f t1 t= f t2
--congT 


-- correctness proof of valiant:
-- the goal is to prove that: φ is a fold (in particular, that φ is valiantFold)

v-c : ∀ {s} (C : Tri s) → TC C (valiantFold C)
v-c {one} one = one-eq
v-c {deeper s₁ s₂} (two U R L) = lemma
  where 
    lemma : ∀ {s₁ s₂} {U : Tri s₁} {R : Mat s₁ s₂} {L : Tri s₂} → φ (two U R L) t≈ valiantOverlap' (valiantFold U) R (valiantFold L)
    lemma {s₁} {s₂} {U} {R} {L} = begin 
      φ (two U R L) 
        ≡⟨ refl ⟩ -- definition
      valiantFold (two U R L) ◂ valiantFold (two U R L) ◂+ two U R L
        ≡⟨ refl ⟩ -- consider triangular parts of product
      (two U⁺ R⁺ L⁺) ◂ (two U⁺ R⁺ L⁺)                ◂+  two U R L
        ≡⟨ refl ⟩ --cong (λ x → x ◂+ two U R L) (lemma-mul U⁺ U⁺ R⁺ R⁺ L⁺ L⁺) ⟩
      two (U⁺ ◂ U⁺) (U⁺ ◂* R⁺ + R⁺ *◂ L⁺) (L⁺ ◂ L⁺)  ◂+  two U R L
        ≡⟨ refl ⟩ --lemma-plus (U⁺ ◂ U⁺) U (U⁺ ◂* R⁺ + R⁺ *◂ L⁺) R (L⁺ ◂ L⁺) L ⟩
      two (U⁺ ◂ U⁺ ◂+ U) ((U⁺ ◂* R⁺ + R⁺ *◂ L⁺) + R) (L⁺ ◂ L⁺ ◂+ L)
        ≡⟨ refl ⟩
      two (φ U) ((U⁺ ◂* R⁺ + R⁺ *◂ L⁺) + R) (φ L)
        ≈⟨ congT (v-c U) reflM (v-c L) ⟩ -- cong₂ (λ X Y → two X ((U⁺ ◂* R⁺ + R⁺ *◂ L⁺) + R) Y) {!!} {!!} ⟩ --(v-c U) (v-c L) ⟩
      two U⁺ ((U⁺ ◂* R⁺ + R⁺ *◂ L⁺) + R) L⁺
        ≈⟨ sub-correct U⁺ R L⁺ ⟩ --sub-correct U⁺ R L⁺ ⟩ 
      two U⁺ (valiantOverlap U⁺ R L⁺) L⁺
        ≡⟨ refl ⟩
      valiantOverlap' U⁺ R L⁺  ∎
        where open EqR (record { Carrier = Tri (deeper s₁ s₂); _≈_ = _t≈_; isEquivalence = isEquivalenceT })
              U⁺ : Tri s₁
              U⁺ = valiantFold U
              L⁺ : Tri s₂
              L⁺ = valiantFold L
              R⁺ : Mat s₁ s₂
              R⁺ = valiantOverlap U⁺ R L⁺


{-
    lemma : ∀ {s₁ s₂} {U : Tri s₁} {R : Mat s₁ s₂} {L : Tri s₂} → φ (two U R L) ≡ valiantOverlap' (φ U) R (φ L)
    lemma {_} {_} {U} {R} {L} = begin 
      φ (two U R L) 
        ≡⟨ refl ⟩ -- definition
      valiantFold (two U R L) ◂ valiantFold (two U R L) ◂+ two U R L
        ≡⟨ refl ⟩ -- consider triangular parts of product
      two U⁺ R⁺ L⁺ 
      ◂ 
      two U⁺ R⁺ L⁺ 
      ◂+ 
      two U R L
        ≡⟨ cong (λ x → x ◂+ two U R L) (lemma-mul U⁺ U⁺ L⁺ L⁺ R⁺ R⁺) ⟩
      two (U⁺ ◂ U⁺) (U⁺ ◂* R⁺ + R⁺ *◂ L⁺) (L⁺ ◂ L⁺) 
      ◂+ 
      two U R L
        ≡⟨ lemma-plus (U⁺ ◂ U⁺) U (L⁺ ◂ L⁺) L (U⁺ ◂* R⁺ + R⁺ *◂ L⁺) R ⟩
      two (U⁺ ◂ U⁺ ◂+ U) 
          ((U⁺ ◂* R⁺
          +
          R⁺ *◂ L⁺)              
          + R) 
          (L⁺ ◂ L⁺ ◂+ L)
        ≡⟨ refl ⟩
      two (φ U)
        ((U⁺ ◂* R⁺
          +
          R⁺ *◂ L⁺)
          + R)
          (φ L)
        ≡⟨ cong₂ (λ X Y → two (φ U) ((X ◂* (valiantOverlap X R Y) + (valiantOverlap X R Y) *◂ Y) + R) (φ L)) (sym (v-c U)) (sym (v-c L)) ⟩


      two (φ U)
        (((φ U) ◂* (valiantOverlap (φ U) R (φ L))
          +
          (valiantOverlap (φ U) R (φ L)) *◂ (φ L))
          + R)
          (φ L)
        ≡⟨ sub-correct (φ U) R (φ L) ⟩ 
      two (φ U) (valiantOverlap (φ U) R (φ L)) (φ L)
        ≡⟨ refl ⟩
      valiantOverlap' (φ U) R (φ L)  ∎
        where U⁺ = valiantFold U
              L⁺ = valiantFold L
              R⁺ = valiantOverlap U⁺ R L⁺-}

{-valiant-correctness : ∀ {s} (C : Tri s) → TC C (valiantFold C)
valiant-correctness {s} C = foldTri-intro {lZero} {Tri} {one} {valiantOverlap'} {φ} {s} {C} refl lemma
  where 
    lemma : ∀ {s₁ s₂} {U : Tri s₁} {R : Mat s₁ s₂} {L : Tri s₂} → φ (two U R L) ≡ valiantOverlap' (φ U) R (φ L)
    lemma {_} {_} {U} {R} {L} = begin 
      φ (two U R L) 
        ≡⟨ refl ⟩ -- definition
      valiantFold (two U R L) ◂ valiantFold (two U R L) ◂+ two U R L
        ≡⟨ refl ⟩ -- consider triangular parts of product
      two U⁺ R⁺ L⁺ 
      ◂ 
      two U⁺ R⁺ L⁺ 
      ◂+ 
      two U R L
        ≡⟨ cong (λ x → x ◂+ two U R L) (lemma-mul U⁺ U⁺ L⁺ L⁺ R⁺ R⁺) ⟩
      two (U⁺ ◂ U⁺) (U⁺ ◂* R⁺ + R⁺ *◂ L⁺) (L⁺ ◂ L⁺) 
      ◂+ 
      two U R L
        ≡⟨ lemma-plus (U⁺ ◂ U⁺) U (L⁺ ◂ L⁺) L (U⁺ ◂* R⁺ + R⁺ *◂ L⁺) R ⟩
      two (U⁺ ◂ U⁺ ◂+ U) 
          ((U⁺ ◂* R⁺
          +
          R⁺ *◂ L⁺)              
          + R) 
          (L⁺ ◂ L⁺ ◂+ L)
        ≡⟨ refl ⟩
      two (φ U)
        ((U⁺ ◂* R⁺
          +
          R⁺ *◂ L⁺)
          + R)
          (φ L)
        ≡⟨ cong₂ (λ X Y → two (φ U) ((X ◂* (valiantOverlap X R Y) + (valiantOverlap X R Y) *◂ Y) + R) (φ L)) (sym (valiant-correctness U)) {!!} ⟩

--((λ X Y → two (φ U) ((X ◂* R⁺ + R⁺ *◂ Y) + R) (φ L)) valiant-correctness valiant-correctness) -- (X ◂* (valiantOverlap X R Y) + (valiantOverlap X R Y) *◂ Y) + R

      two (φ U)
        (((φ U) ◂* (valiantOverlap (φ U) R (φ L))
          +
          (valiantOverlap (φ U) R (φ L)) *◂ (φ L))
          + R)
          (φ L)
        ≡⟨ sub-correct (φ U) R (φ L) ⟩ 
      two (φ U) (valiantOverlap (φ U) R (φ L)) (φ L)
        ≡⟨ refl ⟩
      valiantOverlap' (φ U) R (φ L)  ∎
        where U⁺ = valiantFold U
              L⁺ = valiantFold L
              R⁺ = valiantOverlap U⁺ R L⁺
-- should prove 

-- second proof is that 
-- begin with "fold introduction" (should be used backwards in derivation)

-- if
-}