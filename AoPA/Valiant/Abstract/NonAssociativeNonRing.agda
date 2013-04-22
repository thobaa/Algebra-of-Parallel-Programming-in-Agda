------------------------------------------------------------------------
-- Nonassocitive non-rings:
-- 
-- * Addition not group.
--   . is commutative.
--   . is associative.
--   . has zero
--   . does not have inverse -> Commutative Monoid
-- Multiplication linear
-- not neccessarily multiplicative identity.
-- Should have annihilating zero.
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
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ
    _+_     : Op₂ Carrier
    _*_     : Op₂ Carrier
    0#      : Carrier
    isNonAssociativeNonRing  : IsNonAssociativeNonRing _≈_ _+_ _*_ 0#

  open IsNonAssociativeNonRing isNonAssociativeNonRing public 
  +-commutativeMonoid : CommutativeMonoid _ _
  +-commutativeMonoid = record { isCommutativeMonoid = +-isCommutativeMonoid }

  open CommutativeMonoid +-commutativeMonoid public using (setoid) renaming (monoid to +-monoid; rawMonoid to +-rawMonoid; semigroup to +-semigroup) 
         --using () -- renaming (group to +-group)
