module AoPA.Data.Tree.Unfold where

open import Relation.Binary.PropositionalEquality 
      using (inspect; [_])
open import Data.Empty using (⊥)
open import Function using (id)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import AoPA.Sets
     using (ℙ; _⊆_; _⊇_; ⊆-refl; singleton;
            _≡_; refl; trans; subst; sym)
open import AoPA.Relations
open import AoPA.Relations.PowerTrans
     using (Λ∈-galois-2; Λ-monotonic; ℰ-functor-⊆; ℰ-monotonic')
open import AoPA.AlgebraicReasoning.Sets
     using (⊆-begin_; _⊆⟨_⟩_; _⊆∎;
            ⊇-begin_; _⊇⟨_⟩_; _⊇∎)
open import AoPA.AlgebraicReasoning.Relations
     using (⊒-begin_; _⊒⟨_⟩_; _⊒∎)
open import AoPA.AlgebraicReasoning.Implications

open import AoPA.Relations.WellFound

open import AoPA.Data.Tree
open import AoPA.Data.Tree.Fold using (foldT)

ε-TreeF : {A B : Set} → (B ← (⊤ ⊎ (A × B × B)))
ε-TreeF _ (inj₁ tt) = ⊥
ε-TreeF b (inj₂ (a , b₁ , b₂)) = (b₁ ≡ b) ⊎ (b₂ ≡ b)

unfoldt-acc : {A B : Set} → (f : B → ⊤ ⊎ (A × B × B)) →
            (b : B) → Acc (ε-TreeF ○ fun f) b → Tree A
unfoldt-acc f b (acc .b h)  with f b
... | inj₁ tt = Null
... | inj₂ (a , b₁ , b₂) =
       Fork a (unfoldt-acc f b₁ (h b₁ (inj₂ (a , b₁ , b₂) , refl , inj₁ refl)))
              (unfoldt-acc f b₂ (h b₂ (inj₂ (a , b₁ , b₂) , refl , inj₂ refl)))

unfoldt : {A B : Set} → (f : B → ⊤ ⊎ (A × B × B)) →
            well-found (ε-TreeF ○ fun f) → B → Tree A
unfoldt f wf b = unfoldt-acc f b (wf b)

isInj₁ : {B : Set} → ⊤ ⊎ B → Set
isInj₁ x = x ≡ inj₁ tt

foldT-unfoldt : {A B : Set} → (f : B → ⊤ ⊎ (A × B × B)) →
    (b : B) → (accb : Acc (ε-TreeF ○ fun f) b) →
        foldT ((fun f) ˘ ○ (fun inj₂)) (λ b → isInj₁ (f b))
            b (unfoldt-acc f b accb)
foldT-unfoldt f b (acc .b h) with f b             | inspect f b
foldT-unfoldt f b (acc .b h) | inj₁ tt            | [ fb≡inj₁ ] = fb≡inj₁
foldT-unfoldt f b (acc .b h) | inj₂ (a , b₁ , b₂) | [ fb≡inj₂ ] = 
         ((a , b₁ , b₂) , 
           (refl , foldT-unfoldt f b₁ (h b₁ (inj₂ (a , b₁ , b₂) , refl , inj₁ refl)) , 
                   foldT-unfoldt f b₂ (h b₂ (inj₂ (a , b₁ , b₂) , refl , inj₂ refl))) , 
            inj₂ (a , b₁ , b₂) , refl , fb≡inj₂)
-- OLD PROOF:
{-foldT-unfoldt : {A B : Set} → (f : B → ⊤ ⊎ (A × B × B)) →
    (b : B) → (accb : Acc (ε-TreeF ○ fun f) b) →
        foldT ((fun f) ˘ ○ (fun inj₂)) (λ b → isInj₁ (f b))
            b (unfoldt-acc f b accb)
foldT-unfoldt f b (acc .b h) with inspect (f b)
foldT-unfoldt f b (acc .b h) | v with-≡ v≡fb        with f b             | v≡fb
foldT-unfoldt f b (acc .b h) | .(f b) with-≡ ≡-refl | inj₁ tt            | fb≡inj₁ = fb≡inj₁
foldT-unfoldt f b (acc .b h) | .(f b) with-≡ ≡-refl | inj₂ (a , b₁ , b₂) | fb≡inj₂ = 
       ((a , b₁ , b₂) , 
         (≡-refl , foldT-unfoldt f b₁ (h b₁ (inj₂ (a , b₁ , b₂) , ≡-refl , inj₁ ≡-refl)) , 
                   foldT-unfoldt f b₂ (h b₂ (inj₂ (a , b₁ , b₂) , ≡-refl , inj₂ ≡-refl))) , 
            inj₂ (a , b₁ , b₂) , ≡-refl , fb≡inj₂)
-}
foldT-to-unfoldt : {A B : Set} → (f : B → ⊤ ⊎ (A × B × B)) →
    (wf : well-found (ε-TreeF ○ fun f)) → 
       (foldT ((fun f) ˘ ○ (fun inj₂)) (λ b → isInj₁ (f b))) ˘ ⊒
          fun (unfoldt f wf)
foldT-to-unfoldt f wf t b foldtfb≡t = 
   subst (λ t → foldT ((fun f) ˘ ○ (fun inj₂)) (λ b → isInj₁ (f b)) b t)
       foldtfb≡t (foldT-unfoldt f b (wf b)) 
