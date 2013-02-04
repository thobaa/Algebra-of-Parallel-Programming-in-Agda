open import Valiant.Abstract.NonAssociativeNonRing

open import Relations
open import Data.Product
open import Data.Unit
open import Relation.Binary.PropositionalEquality

open Relation.Binary.PropositionalEquality.≡-Reasoning

open import Level using () renaming (zero to lZero)

open import Valiant.Concrete.Splitting

module Valiant.Specs.JPSpec {l₂} (NAR : NonAssociativeNonRing lZero l₂) where

import Valiant.Concrete.Tri
import Valiant.Concrete.Tri.Operations
import Valiant.Concrete.Mat
import Valiant.Concrete.Mat.Operations
import Valiant.Helper.Definitions
import Valiant.Algorithm.Algorithm
open Valiant.Concrete.Tri NAR
open Valiant.Concrete.Tri.Operations NAR
open Valiant.Concrete.Mat.Operations NAR
open Valiant.Concrete.Mat NAR
open Valiant.Helper.Definitions NAR
open Valiant.Algorithm.Algorithm NAR

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




-- different spec:
TC : ∀ {s} → Tri s ← Tri s
TC C X = X ◂ X ◂+ C ≡ X

-- spec for rectangle
SubTC : ∀ {s₁ s₂} → Tri (deeper s₁ s₂) ← Mat s₁ s₂
SubTC (two U R L) X = U ◂* X + (X *◂ L + R) ≡ X

-- give name to valiant eq
φ : ∀ {s} → Tri s → Tri s
φ X = valiantFold X ◂ valiantFold X ◂+ X

-- these two are not very important.
lemma-mul : ∀ {s₁ s₂} (U₁ U₂ : Tri s₁) (L₁ L₂ : Tri s₂) (R₁ R₂ : Mat s₁ s₂) → 
  two U₁ R₁ L₁ ◂ two U₂ R₂ L₂ ≡ two (U₁ ◂ U₂) (U₁ ◂* R₂ + R₁ *◂ L₂) (L₁ ◂ L₂)
lemma-mul = {!!}

lemma-plus : ∀ {s₁ s₂} (U₁ U₂ : Tri s₁) (L₁ L₂ : Tri s₂) (R₁ R₂ : Mat s₁ s₂) → 
  two U₁ R₁ L₁ ◂+ two U₂ R₂ L₂ ≡ two (U₁ ◂+ U₂) (R₁ + R₂) (L₁ ◂+ L₂)
lemma-plus = {!!}

-- this is specifying equation for rectangle:
{-lemma-rect : ∀ {
  ((valiantFold T₁ ◂* valiantOverlap (valiantFold T₁) R (valiantFold T₂)
          +
          valiantOverlap (valiantFold T₁) R (valiantFold T₂) *◂ valiantFold T₂)
          + R)
-}

-- valiantOverlap satisfies the SubTC:
-- this is an important part of the proof!
valiant-sub-correctness : ∀ {s₁ s₂} {U : Tri s₁} {R : Mat s₁ s₂} {L : Tri s₂ } → SubTC (two U R L) (valiantOverlap U R L)
valiant-sub-correctness = {!!}




lemma : ∀ {s₁ s₂} {U : Tri s₁} {R : Mat s₁ s₂} {L : Tri s₂} → 
  φ (two U R L) ≡ valiantOverlap' (φ U) R (φ L)
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
        ≡⟨ cong (λ X → two (φ U) X (φ L)) {!valiant-sub-correctness!} ⟩
      -- GAP IS HERE!
      -- 
      -- !!! 
      two (φ U) (valiantOverlap (φ U) R (φ L)) (φ L)
        ≡⟨ refl ⟩
      {!!}
      --valiantOverlap' (φ U) R (φ L)  ∎
        where U⁺ = valiantFold U
              L⁺ = valiantFold L
              R⁺ = valiantOverlap U⁺ R L⁺
          

-- correctness proof of valiant:
valiant-correctness : ∀ {s} {C : Tri s} → TC C (valiantFold C)
valiant-correctness {s} {C} = foldTri-intro {lZero} {Tri} {one} {valiantOverlap'} {φ} {s} {C} refl lemma
-- should prove 

-- second proof is that 
-- begin with "fold introduction" (should be used backwards in derivation)

-- if