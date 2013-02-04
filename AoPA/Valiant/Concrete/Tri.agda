open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂)
open import Data.Product using (_×_; _,_)

open import Valiant.Abstract.NonAssociativeNonRing
open import Valiant.Concrete.Splitting
import Valiant.Concrete.Mat


open Relation.Binary.PropositionalEquality.≡-Reasoning
module Valiant.Concrete.Tri {l₁ l₂} (NAR : NonAssociativeNonRing l₁ l₂) where

import Valiant.Concrete.Mat
import Valiant.Helper.Definitions
import Valiant.Concrete.Mat.Operations
open Valiant.Concrete.Mat.Operations NAR
open Valiant.Concrete.Mat NAR
open Valiant.Helper.Definitions NAR

 
data Tri : Splitting → Set l₁ where
  one : Tri one
  two : ∀ {s₁ s₂} → Tri s₁ → Mat s₁ s₂ → 
                             Tri s₂ → 
                    Tri (deeper s₁ s₂)

T0 : ∀ {s} -> Tri s
T0 {one} = one
T0 {deeper y y'} = two T0 zeroMat T0

tri1 : ∀ {s₁ s₂} -> Tri (deeper s₁ s₂) -> Tri s₁
tri1 (two y y' y0) = y
tri2 : ∀ {s₁ s₂} -> Tri (deeper s₁ s₂) -> Tri s₂
tri2 (two y y' y0) = y0
rec : ∀ {s₁ s₂} -> Tri (deeper s₁ s₂) -> Mat s₁ s₂
rec (two y y' y0) = y'
split : ∀ {s₁ s₂} -> Tri (deeper s₁ s₂) -> Tri s₁ × Mat s₁ s₂ × Tri s₂
split = ⟨ tri1 , rec , tri2 ⟩

unsplit : ∀ {s₁ s₂} -> Tri s₁ × Mat s₁ s₂ × Tri s₂ -> Tri (deeper s₁ s₂)
unsplit (T₁ , R , T₂) = two T₁ R T₂


unsplit∘split≡id : ∀ {s₁ s₂} (t : Tri (deeper s₁ s₂)) -> unsplit ( split t) ≡ t
unsplit∘split≡id (two T₁ R T₂) = refl


foldTri : ∀ {b} {s : Splitting} {B : Splitting -> Set b} → (one' : B one) → (two' : ∀ {s₁ s₂} -> B s₁ -> Mat s₁ s₂ -> B s₂ -> B (deeper s₁ s₂) ) → Tri s → B s
foldTri one' two' one = one'
foldTri one' two' (two T₁ R T₂) = two' (foldTri one' two' T₁) R (foldTri one' two' T₂)



foldTri-intro :
  -- Stuff:
  ∀ {a} 
  {A : Splitting → Set a} 
  {one' : A one} 
  {f : ∀ {s1' s2'} → A s1' → Mat s1' s2' → A s2' → A (deeper s1' s2')} 
  {h : ∀ {s} → Tri s → A s} 
  {s : Splitting} 
  {t : Tri s}
  → 
  -- Proofs: 
  (h one) ≡ one' → 
  (∀ {s1} {s2} {t1 : Tri s1} 
               {t2 : Tri s2}
               {r  : Mat s1 s2} → 
  (h (two t1 r t2)) ≡ f (h t1) r (h t2)) → 
  -- Conclusion:
  h t ≡ foldTri one' f t
foldTri-intro {a} {A} {one'} {f} {h} {one} {one} pf1 pf2 = pf1
foldTri-intro {a} {A} {one'} {f} {h} {(deeper s1 s2)} {two t1 r t2} pf1 pf2 = begin 
  h (two t1 r t2) 
    ≡⟨ pf2 {s1} {s2} {t1} {t2} {r} ⟩ 
  f (h t1) r (h t2)
    ≡⟨ cong₂ (λ x y → f x r y) (foldTri-intro {a} {A} {one'} {f} {h} {s1} {t1} pf1 pf2) (foldTri-intro {a} {A} {one'} {f} {h} {s2} {t2} pf1 pf2) ⟩ 
  f (foldTri one' f t1) r (foldTri one' f t2) ∎


-- λ t₁ r t₂ -> two t₁ (valiantOverlap t₁ r t₂) t₂


-- splitmat is fixed pt of F A = [R + Vec R + Vec R + A × A × A × A]
-- vo is fixedpt of 
-- 
-- X (two T₁ R T₂) = [ id , ? , ? , quad  ] 

-- X (two (T₁, R, T₂)) = 
-- X = 
-- input en ((T × A × T) × (A × A × A × A) × (T × A × T))
-- säg quad : A × A × A × A → SplitMat

-- now, properties: 

-- t₁ (ttadd T₁ T₂) == ttadd (t₁ T₁) (t₁ T₂)
-- split (ttadd T₁ T₂) == ttadd (