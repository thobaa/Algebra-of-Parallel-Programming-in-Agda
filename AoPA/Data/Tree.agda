module Data.Tree where


-- fixed by Thomas!
open import Sets using (_≡_; refl)
open import Data.Product using (_×_; _,_)
open import Level using (Level)

data Tree (A : Set) : Set where
  Null : Tree A
  Fork : A → Tree A → Tree A → Tree A

Fork-injective : {A : Set} {a b : A} {t u v w : Tree A} →
   Fork a t u ≡ Fork b v w → (a ≡ b) × (t ≡ v) × (u ≡ w)
Fork-injective refl = (refl , refl , refl)

foldt : {b : Level} {A : Set} {B : Set b} → ((A × B × B) → B) → B → Tree A → B
foldt f e Null = e
foldt f e (Fork a t u) = f (a , foldt f e t , foldt f e u)

-- Not neccessary anymore because of Agda magic
--foldt₁ : {A : Set}{B : Set1} → ((A × B × B) → B) → B → Tree A → B
--foldt₁ f e Null = e
--foldt₁ f e (Fork a t u) = f (a , foldt₁ f e t , foldt₁ f e u)