{-# OPTIONS --universe-polymorphism #-}

module AoPA.AlgebraicReasoning.Equality where

open import Level

import Relation.Binary.PropositionalEquality
        using (_≡_)
        renaming (refl to ≡-refl; trans to ≡-trans)
open Relation.Binary.PropositionalEquality 
  -- could be public, but requires changes in several places

import AoPA.AlgebraicReasoning.PolyPreorderReasoning as PPR

  -- shall we make it more level-polymorphic?

module ≡-reasoning = PPR.UnaryCarrier {zero} {zero} (λ A → A) _≡_ ≡-refl ≡-trans
   renaming (begin_ to ≡-begin_ ; _∼⟨_⟩_ to _≡⟨_⟩_ ; _∎ to _≡∎)
open ≡-reasoning public 
