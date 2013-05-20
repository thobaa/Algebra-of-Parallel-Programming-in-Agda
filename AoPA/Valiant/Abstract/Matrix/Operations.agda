-- here we put mathematical operations for matrixes and vectors.

-- TODO 
-- * scalar multiplication
-- * pointwise multiplication.

open import Data.Nat as ℕ using (ℕ; zero; suc; _≤?_; _≤_) 
open import Data.Vec using (Vec; []; _∷_; foldr; map; zip; reverse)
open import Function using (_∘_; id)
open import Data.Product using (uncurry; uncurry′; <_,_>; proj₂)
open import Data.Fin using (inject+; raise; Fin; toℕ; fromℕ≤) renaming (zero to f0; suc to fsuc)
open import Data.Fin.Props using (inject+-lemma; fromℕ≤-toℕ)
open import Relation.Nullary using (yes; no)
open import Data.Empty using (⊥-elim)
import Relation.Binary.EqReasoning as EqR
open import Relation.Binary.PropositionalEquality as PropEq using (cong; cong₂; refl; sym; _≡_)

open import Valiant.Abstract.NonAssociativeNonRing
module Valiant.Abstract.Matrix.Operations {l₁ l₂} (NAR : NonAssociativeNonRing l₁ l₂) where

import Valiant.Helper.Definitions
open Valiant.Helper.Definitions NAR using ()

import Valiant.Abstract.Matrix as Matrix
open Matrix NAR

open NonAssociativeNonRing NAR renaming (zero to R-zero; _+_ to _R+_; _*_ to _R*_; _≈_ to _R≈_; +-identity to R+-identity; sym to R-sym; trans to R-trans)

-- Dot product
infix 7 _∙_
_∙_ : ∀ {n} → Vector n → Vector n → Carrier
_∙_ {zero} u v = 0# -- this is bad, because it adds an extra zero always.
_∙_ {suc n} u v = (u f0 R* v f0) R+ _∙_ {n} (λ i → u (fsuc i)) (λ i → v (fsuc i))

trans-∙ : {x y : Carrier} → x R≈ y → x R≈ y R+ 0#
trans-∙ x≈y = R-trans x≈y (R-sym (proj₂ R+-identity _))

-- Exterior product
infix 7 _⊗_
_⊗_ : {n m : ℕ} → Vector n → Vector m → Matrix n m 
_⊗_ u v i j = u i R* v j

-- Multiplication by Scalar
infix 7 _sV*_
_sV*_ : {n : ℕ} → Carrier → Vector n → Vector n 
_sV*_ x v i = x R* v i

_Vs*_ : {n : ℕ} → Vector n → Carrier → Vector n
_Vs*_ v x i = v i R* x

infix 6 _V+_
_V+_ : ∀ {n} → Vector n → Vector n → Vector n
u V+ v = λ i → u i R+ v i

-- Vector equality
infix 4 _V≈_
_V≈_ : ∀ {n} → Vector n → Vector n → Set l₂
u V≈ v = (i : _) → u i R≈ v i


-- Matrix addition
infix 6 _+_
_+_ : ∀ {m n} -> Matrix m n -> Matrix m n -> Matrix m n
_+_ A B = λ i j → (A i j) R+ (B i j)

-- Matrix multiplication
infix 7 _*_
_*_ : ∀ {m n p} → Matrix m n → Matrix n p → Matrix m p
A * B = λ i j → (λ k → A i k) ∙ (λ k → B k j)

-- Matrix vector multiplication
infix 7 _MV*_
_MV*_ : {m n : ℕ} → Matrix m n → Vector n → Vector m
A MV* v = λ i → (row i A) ∙ v

infix 7 _VM*_
_VM*_ : {m n : ℕ} → Vector m → Matrix m n → Vector n
v VM* A = λ i → v ∙ col i A




infix 4 _M≈_
_M≈_ : ∀ {m n} → Matrix m n → Matrix m n → Set l₂
A M≈ B = (i : _) (j : _) → A i j R≈ B i j

-- inject and raise (might belong more in a "properties" file)
private
  toℕ<n : {n : ℕ} (i : Fin n) → suc (toℕ i) ≤ n
  toℕ<n {zero} ()
  toℕ<n {suc n} f0 = ℕ.s≤s ℕ.z≤n
  toℕ<n {suc n} (fsuc i) = ℕ.s≤s (toℕ<n i)
  suc-inject+ : (m n : ℕ) (i : Fin m) → suc (toℕ (inject+ n i)) ≤ m
  suc-inject+ m n i = begin 
    suc (toℕ (inject+ n i)) 
      ≡⟨ cong suc (sym (inject+-lemma n i)) ⟩
    suc (toℕ i) 
      ≤⟨ toℕ<n i ⟩
    m ∎
    where open ℕ.≤-Reasoning
  
  fromℕ≤-lemma : (m n : ℕ) (i : Fin m) (p : suc (toℕ (inject+ n i)) ≤ m) → i ≡ fromℕ≤ p
  fromℕ≤-lemma m n i p = begin 
    i 
      ≡⟨ sym (fromℕ≤-toℕ i (toℕ<n i)) ⟩ 
    fromℕ≤ (toℕ<n i)
      ≡⟨ lemma m n i (toℕ<n i) p ⟩
    fromℕ≤ p ∎
    where open PropEq.≡-Reasoning
          lemma : (m n : ℕ) (i : Fin m) (p : suc (toℕ i) ≤ m) (q : suc (toℕ (inject+ n i)) ≤ m) → fromℕ≤ p ≡ fromℕ≤ q
          lemma .(suc n0) n' f0 (ℕ.s≤s {.0} {n0} ℕ.z≤n) (ℕ.s≤s ℕ.z≤n) = PropEq.refl
          lemma .(suc (suc n0)) n' (fsuc i') (ℕ.s≤s (ℕ.s≤s {.(toℕ i')} {n0} m≤n)) (ℕ.s≤s (ℕ.s≤s m≤n')) = begin 
            fsuc (fromℕ≤ (ℕ.s≤s m≤n))
              ≡⟨ cong fsuc (lemma (suc n0) n' i' (ℕ.s≤s m≤n) (ℕ.s≤s m≤n')) ⟩ 
            fsuc (fromℕ≤ (ℕ.s≤s m≤n')) ∎
inject-Four : {m n o p : ℕ} → (A : Matrix m n) (B : Matrix m o) (C : Matrix p n) (D : Matrix p o) →
                (i : Fin m) → (j : Fin n) → A i j R≈ Four A B C D (inject+ p i) (inject+ o j) 
inject-Four {m} {n} {o} {p} A B C D i j with suc (Data.Fin.toℕ (inject+ p i)) ≤? m | suc (Data.Fin.toℕ (inject+ o j)) ≤? n 
inject-Four {m} {n} {o} {p} A B C D i j | yes p' | yes p'' = reflexive (cong₂ A (fromℕ≤-lemma m p i p') (fromℕ≤-lemma n o j p''))
inject-Four {m} {n} {o} {p} A B C D i j | yes p' | no ¬p = ⊥-elim (¬p (suc-inject+ n o j))
inject-Four {m} {n} {o} {p} A B C D i j | no ¬p | _ = ⊥-elim (¬p (suc-inject+ m p i))
{-
raise-Four : {m n o p : ℕ} → (A : Matrix m n) (B : Matrix m o) (C : Matrix p n) (D : Matrix p o) →
                (i : Fin p) → (j : Fin o) → D i j R≈ Four A B C D (raise m i) (raise n j) 
raise-Four {m} {n} {o} {p} A B C D i j with suc (toℕ (raise m i)) ≤? m | suc (toℕ (raise n j)) ≤? n 
raise-Four A B C D i j | yes p' | _ = {!!}
raise-Four A B C D i j | no ¬p | yes p' = {!!}
raise-Four A B C D i j | no ¬p | no ¬p' = {!!} -- den ok.
-}
-- If Four A B C D ≈ Four A' B' C' D', then A = A' ... 
M≈-reduce₁ : {m n o p : ℕ} → (A A' : Matrix m n) (B B' : Matrix m o) (C C' : Matrix p n) (D D' : Matrix p o) → Four A B C D M≈ Four A' B' C' D' → A M≈ A'
M≈-reduce₁ {m} {n} {o} {p} A A' B B' C C' D D' Four≈Four i j = begin 
  A i j 
    ≈⟨ inject-Four A B C D i j ⟩ 
  Four A B C D (inject+ p i) (inject+ o j)
    ≈⟨ Four≈Four (inject+ p i) (inject+ o j) ⟩ 
  Four A' B' C' D' (inject+ p i) (inject+ o j)
    ≈⟨ R-sym (inject-Four A' B' C' D' i j) ⟩ 
  A' i j ∎
  where open EqR setoid
{-
M≈-reduce₄ : {m n o p : ℕ} → (A A' : Matrix m n) (B B' : Matrix m o) (C C' : Matrix p n) (D D' : Matrix p o) → Four A B C D M≈ Four A' B' C' D' → D M≈ D'
M≈-reduce₄ {m} {n} {o} {p} A A' B B' C C' D D' Four≈Four i j = begin 
  D i j 
    ≈⟨ raise-Four A B C D i j ⟩ 
  Four A B C D (raise m i) (raise n j)
    ≈⟨ Four≈Four (raise m i) (raise n j) ⟩ 
  Four A' B' C' D' (raise m i) (raise n j)
    ≈⟨ R-sym (raise-Four A' B' C' D' i j) ⟩ 
  D' i j ∎
  where open EqR setoid
-}

-- Non-associative powers
_^[1+_] : ∀ {n} → Matrix n n → ℕ → Matrix n n
_^[1+_] {n} A i = (foldr (λ _ → Matrix n n) _+_ A ∘ (map (uncurry (_*_))) ∘ (uncurry′ zip) ∘ < id , reverse >) (allPrevious i)
  where
    allPrevious : (k : ℕ) -> Vec (Matrix n n) k
    allPrevious zero     = []
    allPrevious (suc n') = A ^[1+ n' ] ∷ allPrevious n'
