------------------------------------------------------------------------
-- Nonassocitive non-rings:
-- 
-- Addition not group :(,
-- Multiplication linear
-- not neccessarily multiplicative identity.
-- but annihilating 0 follows from axioms!
------------------------------------------------------------------------

module Valiant.Abstract.NonAssociativeNonRing where


open import Relation.Binary
open import Algebra.FunctionProperties
open import Algebra.Structures
open import Function
open import Level

open import Algebra

open import Valiant.Abstract.NonAssociativeNonRing.Structure


record NonAssociativeNonRing c ℓ : Set (suc (c ⊔ ℓ)) where
  infix  8 -_
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ
    _+_     : Op₂ Carrier
    _*_     : Op₂ Carrier
    -_      : Op₁ Carrier
    0#      : Carrier
    isNonAssociativeNonRing  : IsNonAssociativeNonRing _≈_ _+_ _*_ -_ 0#

  open IsNonAssociativeNonRing isNonAssociativeNonRing public 
  +-abelianGroup : AbelianGroup _ _
  +-abelianGroup = record { isAbelianGroup = +-isAbelianGroup }

  open AbelianGroup +-abelianGroup public
         using () renaming (group to +-group)
