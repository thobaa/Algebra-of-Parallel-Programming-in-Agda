module Abstract where

open import Data.Nat
open import Data.Fin using (Fin; fromℕ; fromℕ≤; toℕ;  raise; reduce≥) 
                     renaming (zero to f0; suc to fsuc)

open import Data.Integer using (ℤ; +_; _-_)
                        -- renaming (≥ to z≥)
open import Definitions using (toℤ) renaming (_≥_ to _z≥_; _<_ to _z<_)
open import Data.Empty
open import ZLemmas
open import NatLemmas
open import Algebra
open import Algebra.Structures
open import Data.Product
open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Function
open import Relation.Nullary.Core



open import Level using () renaming (zero to Lzero)
Ring' : Set₁
Ring' = Ring Lzero Lzero

RC : Ring' -> Set
RC = Ring.Carrier

R+ : (a : Ring') -> RC a -> RC a -> RC a
R+ = Ring._+_

R* : (a : Ring') -> RC a -> RC a -> RC a
R* = Ring._*_


R0 : (a : Ring') -> Ring.Carrier a
R0 = Ring.0#

R1 : (a : Ring') -> Ring.Carrier a
R1 = Ring.1#



Vec : (a : Ring') -> ℕ -> Set
Vec a n = Fin n -> RC a

Dot : ∀ {a n} -> Vec a n -> Vec a n -> RC a
Dot {a} {zero} u v = R0 a
Dot {a} {suc n} u v = R+ a (R* a (u f0) (v f0)) (Dot {a}
                                          (λ i → u (fsuc i)) (λ j → v (fsuc j)))

-- stract matrix
Matrix : (a : Ring') -> ℕ -> ℕ -> Set
Matrix a m n = Fin m -> Fin n -> RC a

IsTriangular : ∀ {m n} (a : Ring') -> (d : ℕ) -> (A : Matrix a m n) -> Set
IsTriangular {m} {n} a d A = (i : Fin m) → (j : Fin n) → 
                     (toℤ j - toℤ i z< + d) → A i j ≡ R0 a



-- identity matrix!
Id : ∀ a n -> Matrix a n n
Id a zero () ()
Id a (suc n) f0 f0 = R1 a
Id a (suc n) f0 (fsuc i) = R0 a
Id a (suc n) (fsuc i) f0 = R0 a
Id a (suc n) (fsuc i) (fsuc i') = Id a n i i'

-- Matrix addition
Matrix+ : ∀ a {m n} -> Matrix a m n -> Matrix a m n -> Matrix a m n
Matrix+ a A B = λ i j → R+ a (A i j) (B i j)

-- Matrix multiplication
Matrix* : ∀ a {n m p} -> Matrix a m n -> Matrix a n p -> Matrix a m p
Matrix* a A B = λ i j → Dot {a} (A i) (λ k → B k j)

reduce≤ : ∀ {n m} -> (i : Fin (n + m)) -> (suc (toℕ i) ≤ n) -> Fin n
reduce≤ i pf = fromℕ≤ pf


≰to> : ∀ {m n} -> m ≰ n -> m > n
≰to> {zero} {m} pf = ⊥-elim (pf z≤n)
≰to> {suc n} {zero} pf = s≤s z≤n
≰to> {suc n} {suc n'} pf = s≤s (≰to> (λ z → pf (s≤s z)))

-- Concatenation 
++ : ∀ a {m n o} -> Matrix a m n -> Matrix a m o -> Matrix a m (n + o)
++ a {m} {n} {o} A B i j with suc (toℕ j) ≤? n
...| yes p = A i (reduce≤ j p)
...| no ¬p = B i (reduce≥ j (p≤p (≰to> ¬p)))

-- Concatenation in other dimension
Over : ∀ a {m n o} -> Matrix a m n -> 
                        Matrix a o n -> Matrix a (m + o) n
Over a {m} {n} {o} A B i j with suc (toℕ i) ≤? m
...| yes p = A (reduce≤ i p) j
...| no ¬p = B (reduce≥ i (p≤p (≰to> ¬p))) j