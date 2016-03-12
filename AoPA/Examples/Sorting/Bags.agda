import Relation.Binary 
open Relation.Binary 
     using (Setoid; module Setoid)

open import Level
module AoPA.Examples.Sorting.Bags (c : Level)
                             (ℓ : Level)
                             (elem-s : Setoid c ℓ) where

open import Relation.Nullary using (¬_)
open Relation.Binary 
     using (DecSetoid;     module DecSetoid; 
            IsEquivalence; module IsEquivalence; 
                           module IsDecEquivalence; 
            Rel; Reflexive; Symmetric)
open import Relation.Binary.PropositionalEquality
     using (_≡_) renaming (subst to ≡-subst)

open Setoid elem-s         renaming (Carrier to elem; _≈_ to _≗_)

postulate Bag-decSetoid : DecSetoid c ℓ

Bag : Set c
Bag = DecSetoid.Carrier Bag-decSetoid

_|≈|_ : Rel Bag ℓ
_|≈|_ = DecSetoid._≈_ Bag-decSetoid

|≈|-isEq : IsEquivalence _|≈|_
|≈|-isEq = IsDecEquivalence.isEquivalence (DecSetoid.isDecEquivalence Bag-decSetoid)

|≈|-refl : Reflexive _|≈|_
|≈|-refl = IsEquivalence.refl |≈|-isEq

|≈|-sym : Symmetric _|≈|_
|≈|-sym = IsEquivalence.sym |≈|-isEq

postulate
     bNil : Bag
     bCons : elem → Bag → Bag

     prop-bNil≠bCons : ∀ {a w} → ¬ (bNil |≈| bCons a w)

     prop-bCons-commute : (a b : elem) → (w : Bag) 
          → bCons a (bCons b w) |≈| bCons b (bCons a w)

     |≈|-subst : (P : Bag → Set ℓ) →
             ∀ {w u} → w |≈| u → P w → P u

     |≈|-≡-cong : {a : Set} (f : Bag → a) {x y : Bag} → 
                  x |≈| y → f x ≡ f y 

|≈|-cong : (f : Bag → Bag) {x y : Bag} → x |≈| y → f x |≈| f y 
|≈|-cong f {x} x≡y = |≈|-subst (λ y → f x |≈| f y) (x≡y) |≈|-refl

≡-|≈|-cong : {a : Set} (f : a → Bag) {x y : a} → x ≡ y → f x |≈| f y 
≡-|≈|-cong f {x} x≡y = ≡-subst (λ y → f x |≈| f y) (x≡y) |≈|-refl
