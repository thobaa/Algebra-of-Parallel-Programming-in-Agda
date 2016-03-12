module AoPA.Data.List.ConvFunThm where

open import Relation.Binary.PropositionalEquality
open import Data.Product renaming (map to map-×)
open import Data.List
open import Function using (id)

open import AoPA.Sets
open import AoPA.Relations
open import AoPA.Relations.Function
open import AoPA.Relations.Converse
open import AoPA.Relations.Product using (˘-dist-⨉; ⨉-monotonic)
open import AoPA.Data.List.Fold

open import AoPA.AlgebraicReasoning.Relations
open import AoPA.AlgebraicReasoning.Implications
   
conv-fun-thm : {A B : Set} → (f : B → List A) →
    (R : B ← (A × B)) → (e : ℙ B) →
       (fun f ○ R ⊑ cons ○ (idR ⨉ fun f)) → (fun f · e ⊆ nil) →
          (fun f) ˘ ⊒ foldR R e
conv-fun-thm f R e fR⊑consf fe⊆nil = 
   ⊒-begin 
     (fun f) ˘ 
   ⊒⟨ id-intro-r ⟩
     (fun f) ˘ ○ idR
   ⊒⟨ ○-monotonic-r idR⊒foldR  ⟩ 
     (fun f) ˘ ○ foldR cons nil
   ⊒⟨ foldR-fusion-⊒ ((fun f) ˘) fusion-step fusion-base ⟩ 
     foldR R e  
   ⊒∎
 where fusion-step : R ○ (idR ⨉ (fun f)˘) ⊑ (fun f) ˘ ○ cons
       fusion-step = 
         (⇒-begin 
             fun f ○ R ⊑ cons ○ (idR ⨉ fun f)
          ⇒⟨  fR⊑S⇒R⊑f˘S  ⟩ 
             R ⊑ (fun f)˘ ○ cons ○ (idR ⨉ fun f)
          ⇒⟨ ⊒-trans ○-assocl  ⟩ 
             R ⊑ ((fun f)˘ ○ cons) ○ (idR ⨉ fun f)
          ⇒⟨  ⊒-trans (○-monotonic-r (⨉⊑fun {f = id}{g = f})) ⟩
             R ⊑ ((fun f)˘ ○ cons) ○ fun (map-× id f)
          ⇒⟨ R⊑fS⇒f˘R⊑S  ⟩
             R ○ (fun (map-× id f))˘ ⊑ (fun f)˘ ○ cons
          ⇒⟨  ⊑-trans (○-monotonic-r (˘-monotonic-⇐ (⨉⊑fun {f = id} {g = f}))) ⟩
             R ○ (idR ⨉ fun f)˘ ⊑ (fun f)˘ ○ cons
          ⇒⟨  ⊑-trans (○-monotonic-r (˘-dist-⨉ {R = idR}{S = fun f}) ) ⟩
             R ○ (idR ˘ ⨉ (fun f)˘) ⊑ (fun f)˘ ○ cons
          ⇒⟨  ⊑-trans (○-monotonic-r (⨉-monotonic {R = idR}{T = (fun f)˘} id⊑id˘ ⊑-refl))   ⟩
             R ○ (idR ⨉ (fun f)˘) ⊑ (fun f)˘ ○ cons
          ⇒∎
         ) fR⊑consf
       fusion-base :  Λ ((fun f)˘ ○ ∈) nil ⊇ e
       fusion-base b b∈e = 
         ([] , refl , sym (fe⊆nil (f b) (b , b∈e , refl)))  

