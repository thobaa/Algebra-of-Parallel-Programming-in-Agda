-- Isomorphism of NANRings
open import Valiant.Abstract.NonAssociativeNonRing
open import Algebra.Morphism
open import Relation.Binary
open import Function.Bijection
open import Function.Equality
open import Level using (_⊔_)

module Valiant.Abstract.NonAssociativeNonRing.Isomorphism where

-- a set of nanringhomomorphisms
-- essentially copied from Algebra.Morphism (where there is a ring hom)
record NANRing-Homomorphism {l₁ l₂ l₃ l₄} 
                            (From : NonAssociativeNonRing l₁ l₂) 
                            (To   : NonAssociativeNonRing l₃ l₄) : 
                            Set (l₁ ⊔ l₂ ⊔ l₃ ⊔ l₄) where
       private 
         module F = NonAssociativeNonRing From
         module T = NonAssociativeNonRing To
       open Definitions F.Carrier T.Carrier T._≈_ -- definitions is in Morphism

       field
         ⟦_⟧     : Morphism
         ⟦⟧-cong : ⟦_⟧ Preserves F._≈_ ⟶ T._≈_
         +-hom   : Homomorphic₂ ⟦_⟧ F._+_ T._+_
         *-hom   : Homomorphic₂ ⟦_⟧ F._*_ T._*_
         0-hom   : Homomorphic₀ ⟦_⟧ F.0# T.0# -- <- I don't think this can be proven (since we can't invert)


record NANRing-Isomorphism {l₁ l₂ l₃ l₄} 
                           (From : NonAssociativeNonRing l₁ l₂) 
                           (To   : NonAssociativeNonRing l₃ l₄) :     
                           Set (l₁ ⊔ l₂ ⊔ l₃ ⊔ l₄) where
       field 
         homomorphism : NANRing-Homomorphism From To
       private
         module F = NonAssociativeNonRing From
         module T = NonAssociativeNonRing To
         open NANRing-Homomorphism homomorphism
       field
         bijective    : Bijective {From = F.setoid} {To = T.setoid} 
                                  (record { _⟨$⟩_ = ⟦_⟧; cong = ⟦⟧-cong })

         --inverse-hom : 