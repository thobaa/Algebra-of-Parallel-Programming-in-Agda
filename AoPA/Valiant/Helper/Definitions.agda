open import Data.Vec renaming (zip to zipv; map to mapv)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _≰_; _>_; z≤n; s≤s)
open import Data.Nat.Properties using (commutativeSemiring)
open import Data.Fin using (Fin; toℕ; fromℕ≤; Fin′; _ℕ-ℕ_)
                     renaming (zero to f0; suc to fsuc)
open import Data.Integer using (ℤ; +_; _-_)
open import Valiant.MatrixAlgebra.Definitions using (toℤ) renaming (_≥_ to _z≥_; _<_ to _z<_)
open import Data.Empty using (⊥; ⊥-elim)
open import Algebra using (CommutativeSemiring)
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
