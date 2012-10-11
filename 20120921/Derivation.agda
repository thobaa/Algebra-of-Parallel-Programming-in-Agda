module Derivation where

open import NewTry

open import Relation.Nullary
  using (¬_; Dec; yes; no)
import Relation.Binary
open Relation.Binary
  using (Setoid;        module Setoid;
         DecSetoid;     module DecSetoid;
         DecTotalOrder; module DecTotalOrder;
         Decidable; Transitive)
import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality using () renaming (cong₂ to ≡-cong₂)
open import Function using (id)

open import Data.Empty   using (⊥)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; ∃; _×_; _,_; uncurry; proj₁; proj₂)
open import Data.List    using (List; []; _∷_; foldr)
open import Data.Unit    using (⊤; tt)

open import Sets 
  using (_∪_; _⊇_; ℙ; ⊆-refl; ⊇-refl;
         _≡_)
  renaming (trans to ≡-trans;
            subst to ≡-subst;
            cong to  ≡-cong;
            refl to ≡-refl;
            sym to ≡-sym)

open import Relations
  using (_←_; _˘; fun; _○_; _·_; idR; 
         Λ; 
         ∈; _⊑_; _⊒_; _⨉_; id-intro-r; ⊒-refl;
         ○-monotonic-r)
open import Relations.Coreflexive
open import Data.List.Fold 
  using (nil; cons; foldr₁; foldR; foldR-fusion-⊒;
         idR⊒foldR; foldR-to-foldr; corefl-foldR)

open import AlgebraicReasoning.Sets
     using (⊇-begin_; _⊇⟨_⟩_; _⊇∎)
open import AlgebraicReasoning.Relations
     using (⊑-begin_; _⊑⟨_⟩_; _⊑∎; 
            ⊒-begin_; _⊒⟨_⟩_; _⊒∎)


-- idea: transclosure correct (sum of powers) 
-- split into 3 parts, t1 rec, t2. 
-- t1 t2 commute with transclosure, == recursive part.
-- rec a bit more complicated, but in the end get valiant!

valiant-der : transclosure ⊒ transclose ∘ tembed
valiant-der = ?