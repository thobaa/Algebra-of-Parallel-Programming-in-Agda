-- Standard Library:
open import Data.Nat using (ℕ; _+_; suc; _≤?_; zero; _<_; _≤_; z≤n; s≤s; _≥_; ≤-pred)
open import Data.Nat.Properties using (≰⇒>)
open import Data.Fin using (Fin; toℕ; reduce≥; _ℕ-ℕ_; inject; fromℕ≤)
                     renaming (zero to f0; suc to fsuc)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; cong; cong₂; refl)
open import Data.Empty using (⊥-elim)

-- OWN:
open import Valiant.Abstract.NonAssociativeNonRing using (NonAssociativeNonRing)
import Valiant.Helper.Definitions using (reduce≤; injectF+F)
-- "Deprecated":
--open import Valiant.MatrixAlgebra.NatLemmas using (p≤p)


-- Module containing 
module Valiant.Abstract.Matrix {l₁ l₂} (NAR : NonAssociativeNonRing l₁ l₂) where

open Valiant.Helper.Definitions NAR

-- Abstract vector
Vector : ℕ → Set l₁
Vector n = (i : Fin n) → NonAssociativeNonRing.Carrier NAR

zeroVector : {n : _} → Vector n
zeroVector i = NonAssociativeNonRing.0# NAR

-- Vector concatenation
V++ : ∀ {n m} → Vector n → Vector m → Vector (n + m)
V++ {n} {m} v1 v2 i with suc (toℕ i) ≤? n
V++ v1 v2 i | yes p = v1 (reduce≤ i p)
V++ v1 v2 i | no ¬p = v2 (reduce≥ i (≤-pred (≰⇒> ¬p)))

Two : {n m : ℕ} → Vector n → Vector m → Vector (n + m)
Two {n} u v i with suc (toℕ i) ≤? n 
Two u v i | yes i<n = u (fromℕ≤ i<n)
Two u v i | no ¬i<n = v (reduce≥ i (≤-pred (≰⇒> ¬i<n)))

-- head and tail
head : {n : _} → Vector (suc n) → NonAssociativeNonRing.Carrier NAR
head v = v f0
tail : {n : _} → Vector (suc n) → Vector n
tail v = λ i → v (fsuc i)



-- Abstract matrix
Matrix : ℕ → ℕ → Set l₁
Matrix m n = (i : Fin m) → (j : Fin n) → NonAssociativeNonRing.Carrier NAR

-- Extracts the i:th row of a matrix
row : {m n : ℕ} (i : Fin m) → Matrix m n → Vector n
row i A k = A i k

-- Extracts the j:th column of a matrix
col : {m n : ℕ} (j : Fin n) → Matrix m n → Vector m
col j A k = A k j
-- NOTE: No Identity matrix as no one in ring

-- Zero Matrix
zeroMatrix : ∀ {n} {m} → Matrix n m
zeroMatrix i j = NonAssociativeNonRing.0# NAR

-- Concatenation 
Side : ∀ {m n o} → Matrix m n → Matrix m o → Matrix m (n + o)
Side {m} {n} {o} A B i j with suc (toℕ j) ≤? n
...| yes p = A i (reduce≤ j p)
...| no ¬p = B i (reduce≥ j (≤-pred (≰⇒> ¬p)))

-- Concatenation in other dimension
Over : ∀ {m n o} → Matrix m n → 
                        Matrix o n → Matrix (m + o) n
Over {m} {n} {o} A B i j with suc (toℕ i) ≤? m
...| yes p = A (reduce≤ i p) j
...| no ¬p = B (reduce≥ i (≤-pred (≰⇒> ¬p))) j

-- Four concatenation
Four : ∀ {m n o p} → Matrix m n → Matrix m o → 
                      Matrix p n → Matrix p o → 
                      Matrix (m + p) (n + o)
Four {m} {n} {o} {p} A B 
                       C D i j with suc (toℕ i) ≤? m | suc (toℕ j) ≤? n
Four A B C D i j | yes p₁ | yes p₂ = A (reduce≤ i p₁) (reduce≤ j p₂)
Four A B C D i j | yes p₁ | no ¬p₂ = B (reduce≤ i p₁) (reduce≥ j (≤-pred (≰⇒> ¬p₂)))
Four A B C D i j | no ¬p₁ | yes p₂ = C (reduce≥ i (≤-pred (≰⇒> ¬p₁))) (reduce≤ j p₂)
Four A B C D i j | no ¬p₁ | no ¬p₂ = D (reduce≥ i (≤-pred (≰⇒> ¬p₁))) (reduce≥ j (≤-pred (≰⇒> ¬p₂)))

-- Different Four concatenation
{-
Four' : ∀ {m n} → {rSplit : Fin m} → {cSplit : Fin n} →
        Matrix (toℕ rSplit) (toℕ cSplit) → Matrix (toℕ rSplit) (n ℕ-ℕ fsuc cSplit) → 
        Matrix (m ℕ-ℕ fsuc rSplit) (toℕ cSplit) → Matrix (m ℕ-ℕ fsuc rSplit) (n ℕ-ℕ fsuc cSplit) →
        Matrix m n
Four' {m} {n} {rSplit} {cSplit} A B 
                      C D i j with suc (toℕ i) ≤? (toℕ rSplit) | suc (toℕ j) ≤? (toℕ cSplit)
Four' {rSplit = rSplit} {cSplit = cSplit} A B C D i j | yes p₁ | yes p₂ = A (reduce′ i rSplit p₁) (reduce′ j cSplit p₂)
Four' {rSplit = rSplit} {cSplit = cSplit} A B C D i j | yes p₁ | no ¬p₂ = B (reduce′ i rSplit p₁) (reduce″ j cSplit ¬p₂)
Four' {rSplit = rSplit} {cSplit = cSplit} A B C D i j | no ¬p₁ | yes p₂ = C (reduce″ i rSplit ¬p₁) (reduce′ j cSplit p₂)
Four' {rSplit = rSplit} {cSplit = cSplit} A B C D i j | no ¬p₁ | no ¬p₂ = D (reduce″ i rSplit ¬p₁) (reduce″ j cSplit ¬p₂)
-}


-- Extractions
UL : ∀ {m n} → Matrix m n → (rMax : Fin m) → (cMax : Fin n) → Matrix (toℕ rMax) (toℕ cMax)
UL A rMax cMax i j = A (inject i) (inject j)

UR : ∀ {m n} → Matrix m n → (rMax : Fin m) → (cMin : Fin (suc n)) → Matrix (toℕ rMax) (n ℕ-ℕ cMin)
UR A rMax cMin i j = A (inject i) (injectF+F cMin j)
LL : {m n : _} → Matrix m n → (rMin : Fin (suc m)) → (cMax : Fin n) → Matrix (m ℕ-ℕ rMin) (toℕ cMax)
LL A rMin cMax i j = A (injectF+F rMin i) (inject j)

LR : {m n : _} → Matrix m n → (rMin : Fin (suc m)) → (cMin : Fin (suc n)) → Matrix (m ℕ-ℕ rMin) (n ℕ-ℕ cMin)
LR A rMin cMin i j = A (injectF+F rMin i) (injectF+F cMin j)



{-

smart-indexing₁ : ∀ {m n o p} → (A : Matrix m n) → (B : Matrix m o) → 
                               (C : Matrix p n) → (D : Matrix p o) → 
                      (i : Fin (m + p)) → (j : Fin (n + o)) → (i<m : toℕ i < m) → (j<n : toℕ j < n) →  (Four A B C D i j ≡ A (reduce≤ i i<m) (reduce≤ j j<n))
smart-indexing₁ {m} {n} A B C D i j i<m j<n with suc (toℕ i) ≤? m | suc (toℕ j) ≤? n
smart-indexing₁ A B C D i j i<m j<n | yes p  | yes p' = begin 
  A (Data.Fin.fromℕ≤ p) (Data.Fin.fromℕ≤ p') 
    ≡⟨ cong₂ A (cong fromℕ≤ (proofs-equal p i<m)) (cong fromℕ≤ (proofs-equal p' j<n)) ⟩ 
  A (Data.Fin.fromℕ≤ i<m) (Data.Fin.fromℕ≤ j<n) ∎
  where open PropEq.≡-Reasoning
smart-indexing₁ A B C D i j i<m j<n | yes p' | no ¬p = ⊥-elim (¬p j<n)
smart-indexing₁ A B C D i j i<m j<n | no ¬p  | _ = ⊥-elim (¬p i<m)


smart-indexing₂ : ∀ {m n o p} → (A : Matrix m n) → (B : Matrix m o) → 
                                (C : Matrix p n) → (D : Matrix p o) → 
                      (i : Fin (m + p)) → (j : Fin (n + o)) → (i<m : toℕ i < m) → (¬j<n : ¬ (toℕ j < n)) →  (Four A B C D i j ≡ B (reduce≤ i i<m) (reduce≥ j (≤-pred (≰⇒> ¬j<n))))
smart-indexing₂ {m} {n} A B C D i j i<m j<n with suc (toℕ i) ≤? m | suc (toℕ j) ≤? n
smart-indexing₂ A B C D i j i<m ¬j<n | yes p  | yes p' = ⊥-elim (¬j<n p')
smart-indexing₂ A B C D i j i<m ¬j<n | yes p' | no ¬p = begin 
  B (fromℕ≤ p') (reduce≥ j (≤-pred (≰⇒> ¬p)))
    ≡⟨ cong₂ B (cong fromℕ≤ (proofs-equal p' i<m)) (cong (reduce≥ j) (cong ≤-pred (proofs-equal (≰⇒> ¬p) (≰⇒> ¬j<n)))) ⟩ 
  B (fromℕ≤ i<m) (reduce≥ j (≤-pred (≰⇒> ¬j<n))) ∎
  where open PropEq.≡-Reasoning
smart-indexing₂ A B C D i j i<m ¬j<n | no ¬p  | _ = ⊥-elim (¬p i<m)

-}

--= begin 
  --{!!} ≡⟨ {!!} ⟩ A (Data.Fin.fromℕ≤ i<m) (Data.Fin.fromℕ≤ j<n) ∎
  --where open PropEq.≡-Reasoning

--with Four A B C D | (inspect (Four A B C D))
--...| aa | bb = {!!}
