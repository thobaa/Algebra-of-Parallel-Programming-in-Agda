
open import Data.Vec renaming (zip to zipv; map to mapv)
open import Data.Nat
open import Data.Fin using (Fin; fromℕ; fromℕ≤; toℕ;  raise; reduce≥) 
                     renaming (zero to f0; suc to fsuc)

open import Data.Integer using (ℤ; +_; _-_)
                        -- renaming (≥ to z≥)
open import Matrix.Definitions using (toℤ) renaming (_≥_ to _z≥_; _<_ to _z<_)
open import Data.Empty
open import Matrix.ZLemmas
open import Matrix.NatLemmas
open import Algebra
open import Algebra.Structures
open import Data.Product
open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Function
open import Relation.Nullary.Core

open import Level using () renaming (zero to Lzero)

open import Matrix.NonAssociativeRing

module Matrix.Abstract (NAR : NonAssociativeRing Lzero Lzero) where

R : Set
R = NonAssociativeRing.Carrier NAR

_R+_ : R → R → R
_R+_ = NonAssociativeRing._+_ NAR

_R*_ : R → R → R
_R*_ = NonAssociativeRing._*_ NAR


R0 : R
R0 = NonAssociativeRing.0# NAR



reduce≤ : ∀ {n m} -> (i : Fin (n + m)) -> (suc (toℕ i) ≤ n) -> Fin n
reduce≤ i pf = fromℕ≤ pf


≰to> : ∀ {m n} -> m ≰ n -> m > n
≰to> {zero} {m} pf = ⊥-elim (pf z≤n)
≰to> {suc n} {zero} pf = s≤s z≤n
≰to> {suc n} {suc n'} pf = s≤s (≰to> (λ z → pf (s≤s z)))


Vector : ℕ → Set
Vector n = (i : Fin n) → R


V++ : ∀ {n m} -> Vector n -> Vector m -> Vector (n + m)
V++ {n} {m} v1 v2 i with suc (toℕ i) ≤? n
V++ v1 v2 i | yes p = v1 (reduce≤ i p)
V++ v1 v2 i | no ¬p = v2 (reduce≥ i (p≤p (≰to> ¬p)))

_⊙_ : ∀ {n} → Vector n → Vector n → R
_⊙_ {zero} u v = R0
_⊙_ {suc n} u v = (u f0 R* v f0) R+ _⊙_ {n} (λ i → u (fsuc i)) (λ i → v (fsuc i))
-- Abstract matrix
Matrix : ℕ → ℕ → Set
Matrix m n = (i : Fin m) → (j : Fin n) → R



IsTriangular : ∀ {m n} -> (d : ℕ) -> (A : Matrix m n) -> Set
IsTriangular {m} {n} d A = (i : Fin m) → (j : Fin n) → 
                           (toℤ j - toℤ i z< + d) → A i j ≡ R0


Triangle : ℕ -> Set
Triangle n = Σ (Matrix n n) (λ A → IsTriangular 1 A)

-- identity matrix! Not available!
{-
Id : ∀ a n -> Matrix a n n
Id a zero () ()
Id a (suc n) f0 f0 = R1 a
Id a (suc n) f0 (fsuc i) = R0 a
Id a (suc n) (fsuc i) f0 = R0 a
Id a (suc n) (fsuc i) (fsuc i') = Id a n i i'-}

Zero : ∀ n m -> Matrix n m
Zero n m i j = R0

-- Matrix addition
_M+_ : ∀ {m n} -> Matrix m n -> Matrix m n -> Matrix m n
_M+_ A B = λ i j → (A i j) R+ (B i j)

-- Matrix multiplication

_M*_ : ∀ {m n p} → Matrix m n → Matrix n p → Matrix m p
A M* B = λ i j → (λ k → A i k) ⊙ (λ k → B k j)




-- Non-associative powers
_^[1+_] : ∀ {n} → Matrix n n → ℕ → Matrix n n
_^[1+_] {n} A i = (foldr (λ _ → Matrix n n) _M+_ A ∘ (mapv (uncurry (_M*_))) ∘ (uncurry′ zipv) ∘ < id , reverse >) (allPrevious i)
  where
    allPrevious : (k : ℕ) -> Vec (Matrix n n) k
    allPrevious zero     = []
    allPrevious (suc n') = A ^[1+ n' ] ∷ allPrevious n'





-- Concatenation 
Side : ∀ {m n o} -> Matrix m n -> Matrix m o -> Matrix m (n + o)
Side {m} {n} {o} A B i j with suc (toℕ j) ≤? n
...| yes p = A i (reduce≤ j p)
...| no ¬p = B i (reduce≥ j (p≤p (≰to> ¬p)))

-- Concatenation in other dimension
Over : ∀ {m n o} -> Matrix m n -> 
                        Matrix o n -> Matrix (m + o) n
Over {m} {n} {o} A B i j with suc (toℕ i) ≤? m
...| yes p = A (reduce≤ i p) j
...| no ¬p = B (reduce≥ i (p≤p (≰to> ¬p))) j

Four : ∀ {m n o p} -> Matrix m n -> Matrix m o -> 
                       Matrix p n -> Matrix p o -> 
                       Matrix (m + p) (n + o)
Four {m} {n} {o} {p} A B 
                       C D i j with suc (toℕ i) ≤? m | suc (toℕ j) ≤? n
Four A B C D i j | yes p₁ | yes p₂ = A (reduce≤ i p₁) (reduce≤ j p₂)
Four A B C D i j | yes p₁ | no ¬p₂ = B (reduce≤ i p₁) (reduce≥ j (p≤p (≰to> ¬p₂)))
Four A B C D i j | no ¬p₁ | yes p₂ = C (reduce≥ i (p≤p (≰to> ¬p₁))) (reduce≤ j p₂)
Four A B C D i j | no ¬p₁ | no ¬p₂ = D (reduce≥ i (p≤p (≰to> ¬p₁))) (reduce≥ j (p≤p (≰to> ¬p₂)))