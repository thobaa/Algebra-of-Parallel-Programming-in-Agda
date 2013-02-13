open import Data.Vec renaming (zip to zipv; map to mapv)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _≰_; _>_; z≤n; s≤s)
open import Data.Nat.Properties using (commutativeSemiring)
open import Data.Fin using (Fin; toℕ; fromℕ≤; Fin′; _ℕ-ℕ_)
                     renaming (zero to f0; suc to fsuc)
open import Data.Integer using (ℤ; +_; _-_)

import Relation.Binary.EqReasoning as EqR
open import Valiant.MatrixAlgebra.Definitions using (toℤ) renaming (_≥_ to _z≥_; _<_ to _z<_)
open import Data.Empty using (⊥; ⊥-elim)
open import Algebra
open import Data.Product using (proj₂; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (subst; sym; cong)
open Relation.Binary.PropositionalEquality.≡-Reasoning using (begin_; _≡⟨_⟩_; _∎)

open import Valiant.Abstract.NonAssociativeNonRing

-- "Deprecated"
open import Valiant.MatrixAlgebra.ZLemmas
open import Valiant.MatrixAlgebra.NatLemmas

module Valiant.Helper.Definitions {l₁ l₂} (NAR : NonAssociativeNonRing l₁ l₂) where

open Algebra.CommutativeSemiring commutativeSemiring using (+-identity; +-comm)

-- Ring stuff
R : Set l₁
R = NonAssociativeNonRing.Carrier NAR

infix 5 _R+_
_R+_ : R → R → R
_R+_ = NonAssociativeNonRing._+_ NAR

infix 6 _R*_
_R*_ : R → R → R
_R*_ = NonAssociativeNonRing._*_ NAR


R0 : R
R0 = NonAssociativeNonRing.0# NAR

rearrangeLemma : ∀ {a b}{cm : CommutativeMonoid a b} (x y z å : CommutativeMonoid.Carrier cm) → 
               let _+'_ = CommutativeMonoid._∙_ cm ; _≈'_ = (CommutativeMonoid._≈_ cm) in
               ((x +' y) +' (z +' å)) ≈' ((x +' z) +' (y +' å))
rearrangeLemma {cm = cm} x y z å = ≈begin
                 (x +' y) +' (z +' å) 
                   ≈⟨ sym' (assoc (x +' y) z å) ⟩ 
                 ((x +' y) +' z) +' å 
                   ≈⟨ ∙-cong (assoc x y z) refl ⟩   
                 (x +' (y +' z)) +' å 
                   ≈⟨ ∙-cong (∙-cong refl (comm y z)) refl ⟩   
                 (x +' (z +' y)) +' å 
                   ≈⟨ ∙-cong (sym' (assoc x z y)) refl ⟩   
                 ((x +' z) +' y) +' å 
                   ≈⟨ assoc (x +' z) y å ⟩ 
                 (x +' z) +' (y +' å) ≈∎
  where open EqR (CommutativeMonoid.setoid cm) renaming (begin_ to ≈begin_; _∎ to _≈∎)
        open CommutativeMonoid cm renaming (_∙_ to _+'_; sym to sym')

rearrangeLemma' : ∀ {a b}{cm : CommutativeMonoid a b} (x y a b c d : CommutativeMonoid.Carrier cm) → 
                let _+'_ = CommutativeMonoid._∙_ cm; _≈'_ = CommutativeMonoid._≈_ cm in 
                x ≈' (a +' b) → y ≈' (c +' d) → 
                (x +' y) ≈' ((a +' c) +' (b +' d)) 
rearrangeLemma' {cm = cm} x y a b c d x≈a∙b y≈c∙d = ≈begin 
                  x +' y 
                    ≈⟨ ∙-cong x≈a∙b y≈c∙d ⟩ 
                  a +' b +' (c +' d)
                    ≈⟨ rearrangeLemma {cm = cm} a b c d ⟩ 
                  (a +' c) +' (b +' d) ≈∎
  where open EqR (CommutativeMonoid.setoid cm) renaming (begin_ to ≈begin_; _∎ to _≈∎)
        open CommutativeMonoid cm renaming (_∙_ to _+'_) 

sumLemma : ∀ {a b} {cm : CommutativeMonoid a b} {x y : CommutativeMonoid.Carrier cm} → let _+'_ = CommutativeMonoid._∙_ cm; ε = CommutativeMonoid.ε cm; _≈'_ = CommutativeMonoid._≈_ cm in x ≈' ε → y ≈' ε → (x +' y) ≈' ε
sumLemma {cm = cm} {x} {y} x≈ε y≈ε = ≈begin 
           x +' y 
             ≈⟨ ∙-cong x≈ε y≈ε ⟩
           ε +' ε
             ≈⟨ identityˡ ε ⟩
           ε ≈∎
  where open CommutativeMonoid cm renaming (_∙_ to _+'_)
        open EqR setoid renaming (begin_ to ≈begin_; _∎ to _≈∎)

-- Fin stuff 
f1 : ∀ {n} → Fin (suc (suc n))
f1 = fsuc f0



-- reduce 
reduce≤ : ∀ {n m} -> (i : Fin (n + m)) -> (suc (toℕ i) ≤ n) -> Fin n
reduce≤ i pf = fromℕ≤ pf

postulate 
  reduce′ : ∀ {n} → (i r : Fin n) → (suc (toℕ i) ≤ toℕ r) → Fin′ r
--reduce′ = {!!} 

postulate
  reduce″ : ∀ {n} → (i r : Fin n) → (suc (toℕ i) ≤ toℕ r → ⊥) → Fin (n ℕ-ℕ fsuc r)

-- inject
injectF+F : ∀ {n} → (base : Fin (suc n)) → (i : Fin (n ℕ-ℕ base)) → Fin n
injectF+F {zero} f0 ()
injectF+F {zero} (fsuc ()) i
injectF+F {suc n} f0 i = i
injectF+F {suc n} (fsuc base') i = fsuc (injectF+F base' i)

-- raise a Fin m
raise' : ∀ {m} -> Fin m -> (n : ℕ) -> Fin (m + n)
raise' {m} i zero = subst Fin (sym (proj₂ +-identity m)) i
raise' {m} i (suc n) = subst Fin (begin suc (m + n) 
                                        ≡⟨ cong suc (+-comm m n) ⟩
                                        suc n + m
                                        ≡⟨ +-comm (suc n) m ⟩
                                        m + suc n ∎) (fsuc (raise' i n)) 


-- Nat stuff
≰to> : ∀ {m n} -> m ≰ n -> m > n
≰to> {zero} {m} pf = ⊥-elim (pf z≤n)
≰to> {suc n} {zero} pf = s≤s z≤n
≰to> {suc n} {suc n'} pf = s≤s (≰to> (λ z → pf (s≤s z)))

-- Pair stuff
⟨_,_,_⟩ : {a b c d : Set l₁} -> 
        (a → b) → (a → c) → (a → d) →
        a → (b × c × d)
⟨ f , g , h ⟩ x = f x , g x , h x
