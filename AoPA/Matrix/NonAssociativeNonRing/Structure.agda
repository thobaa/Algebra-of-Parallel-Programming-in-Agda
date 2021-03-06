
module Matrix.NonAssociativeNonRing.Structure where

open import Relation.Binary

open import Algebra.Structures

import Algebra.FunctionProperties as FunctionProperties
open import Data.Product
open import Function
open import Level using (_⊔_)
import Relation.Binary.EqReasoning as EqR

open FunctionProperties using (Op₁; Op₂)

record IsNonAssociativeNonRing
         {a ℓ} {A : Set a} (≈ : Rel A ℓ)
         (_+_ _*_ : Op₂ A) (-_ : Op₁ A) (0# : A) : Set (a ⊔ ℓ) where
  open FunctionProperties ≈
  field
    +-isAbelianGroup : IsAbelianGroup ≈ _+_ 0# -_
    *-cong           : _*_ Preserves₂ ≈ ⟶ ≈ ⟶ ≈
    distrib          : _*_ DistributesOver _+_

  open IsAbelianGroup +-isAbelianGroup public
         renaming ( assoc               to +-assoc
                  ; ∙-cong              to +-cong
                  ; isSemigroup         to +-isSemigroup
                  ; identity            to +-identity
                  ; isMonoid            to +-isMonoid
                  ; inverse             to -‿inverse
                  ; ⁻¹-cong             to -‿cong
                  ; isGroup             to +-isGroup
                  ; comm                to +-comm
                  ; isCommutativeMonoid to +-isCommutativeMonoid
                  )

  zero : Zero 0# _*_
  zero = (zeroˡ , zeroʳ)
    where
    open EqR (record { isEquivalence = isEquivalence })

    zeroˡ : LeftZero 0# _*_
    zeroˡ x = begin
        0# * x                              ≈⟨ sym $ proj₂ +-identity _ ⟩
       (0# * x) +            0#             ≈⟨ refl ⟨ +-cong ⟩ sym (proj₂ -‿inverse _) ⟩
       (0# * x) + ((0# * x)  + - (0# * x))  ≈⟨ sym $ +-assoc _ _ _ ⟩
      ((0# * x) +  (0# * x)) + - (0# * x)   ≈⟨ sym (proj₂ distrib _ _ _) ⟨ +-cong ⟩ refl ⟩
             ((0# + 0#) * x) + - (0# * x)   ≈⟨ (proj₂ +-identity _ ⟨ *-cong ⟩ refl)
                                                 ⟨ +-cong ⟩
                                               refl ⟩
                    (0# * x) + - (0# * x)   ≈⟨ proj₂ -‿inverse _ ⟩
                             0#             ∎

    zeroʳ : RightZero 0# _*_
    zeroʳ x = begin
      x * 0#                              ≈⟨ sym $ proj₂ +-identity _ ⟩
      (x * 0#) + 0#                       ≈⟨ refl ⟨ +-cong ⟩ sym (proj₂ -‿inverse _) ⟩
      (x * 0#) + ((x * 0#) + - (x * 0#))  ≈⟨ sym $ +-assoc _ _ _ ⟩
      ((x * 0#) + (x * 0#)) + - (x * 0#)  ≈⟨ sym (proj₁ distrib _ _ _) ⟨ +-cong ⟩ refl ⟩
      (x * (0# + 0#)) + - (x * 0#)        ≈⟨ (refl ⟨ *-cong ⟩ proj₂ +-identity _)
                                               ⟨ +-cong ⟩
                                             refl ⟩
      (x * 0#) + - (x * 0#)               ≈⟨ proj₂ -‿inverse _ ⟩
      0#                                  ∎

-- maybe add one with multiplicative 1 also.