open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Product
open import Data.Sum

import Matrix.Abstract
import Matrix.NewNewSplit
import Matrix.Tri
open import Matrix.STree

open import Matrix.NonAssociativeNonRing

open import Level using () renaming (zero to Lzero)

open import Data.Unit
open import Function


open Relation.Binary.PropositionalEquality.≡-Reasoning
module Matrix.TriFold (NAR : NonAssociativeNonRing Lzero Lzero) where


open Matrix.Abstract (NAR)
open Matrix.NewNewSplit (NAR)
open Matrix.Tri (NAR)
-- here is a problem!
--α : ∀ {s1 R s2} → ⊤ ⊎ (Tri s1 × SplitMat s1 s2 × Tri s2) → Tri (deeper s1 s2)
--α = {!!}

--F : ∀ {a s1 s2} → (∀ {s} → Tri s → a s) → (Tri s1 × SplitMat s1 s2 × Tri s2 → a s1 × SplitMat s1 s2 × a s2)
--F h = {!!}

-- similar to foldR-induction-⊒ in List.Fold
foldTri-intro : ∀ {a} {A : Splitting → Set a} 
  -- Stuff:
  {one' : A one} 
  {f : ∀ {s1' s2'} → A s1' → SplitMat s1' s2' → A s2' → A (deeper s1' s2')} 
  {h : ∀ {s} → Tri s → A s} 
  {s : Splitting} 
  {t : Tri s}
  → 
  -- Proofs: 
  (h one) ≡ one' → 
  (∀ {s1} {s2} {t1 : Tri s1} 
               {t2 : Tri s2}
               {r  : SplitMat s1 s2} → 
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


-- now, recursion stuff
-- X 