-- Standard Library:
open import Data.Nat using (ℕ; _+_; suc; _≤?_; zero)
open import Data.Fin using (Fin; toℕ; reduce≥; _ℕ-ℕ_; inject)
                     renaming (zero to f0; suc to fsuc)
open import Relation.Nullary.Core using (yes; no)

-- OWN:
open import Valiant.Abstract.NonAssociativeNonRing using (NonAssociativeNonRing)
import Valiant.Helper.Definitions using (R; R0; reduce≤; ≰to>; reduce′; reduce″; injectF+F)
-- "Deprecated":
open import Valiant.MatrixAlgebra.NatLemmas using (p≤p)


-- Module containing 
module Valiant.Abstract.Matrix {l₁ l₂} (NAR : NonAssociativeNonRing l₁ l₂) where

open Valiant.Helper.Definitions NAR

-- Abstract vector
Vector : ℕ → Set l₁
Vector n = (i : Fin n) → R

-- Vector concatenation
V++ : ∀ {n m} -> Vector n -> Vector m -> Vector (n + m)
V++ {n} {m} v1 v2 i with suc (toℕ i) ≤? n
V++ v1 v2 i | yes p = v1 (reduce≤ i p)
V++ v1 v2 i | no ¬p = v2 (reduce≥ i (p≤p (≰to> ¬p)))

-- Abstract matrix
Matrix : ℕ → ℕ → Set l₁
Matrix m n = (i : Fin m) → (j : Fin n) → R

-- NOTE: No Identity matrix as no one in ring

-- Zero Matrix
zeroMatrix : ∀ {n} {m} -> Matrix n m
zeroMatrix i j = R0

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

-- Four concatenation
Four : ∀ {m n o p} -> Matrix m n -> Matrix m o -> 
                       Matrix p n -> Matrix p o -> 
                       Matrix (m + p) (n + o)
Four {m} {n} {o} {p} A B 
                       C D i j with suc (toℕ i) ≤? m | suc (toℕ j) ≤? n
Four A B C D i j | yes p₁ | yes p₂ = A (reduce≤ i p₁) (reduce≤ j p₂)
Four A B C D i j | yes p₁ | no ¬p₂ = B (reduce≤ i p₁) (reduce≥ j (p≤p (≰to> ¬p₂)))
Four A B C D i j | no ¬p₁ | yes p₂ = C (reduce≥ i (p≤p (≰to> ¬p₁))) (reduce≤ j p₂)
Four A B C D i j | no ¬p₁ | no ¬p₂ = D (reduce≥ i (p≤p (≰to> ¬p₁))) (reduce≥ j (p≤p (≰to> ¬p₂)))

-- Different Four concatenation
Four' : ∀ {m n} -> {rSplit : Fin m} → {cSplit : Fin n} →
        Matrix (toℕ rSplit) (toℕ cSplit) -> Matrix (toℕ rSplit) (n ℕ-ℕ fsuc cSplit) -> 
        Matrix (m ℕ-ℕ fsuc rSplit) (toℕ cSplit) -> Matrix (m ℕ-ℕ fsuc rSplit) (n ℕ-ℕ fsuc cSplit) →
        Matrix m n
Four' {m} {n} {rSplit} {cSplit} A B 
                      C D i j with suc (toℕ i) ≤? (toℕ rSplit) | suc (toℕ j) ≤? (toℕ cSplit)
Four' {rSplit = rSplit} {cSplit = cSplit} A B C D i j | yes p₁ | yes p₂ = A (reduce′ i rSplit p₁) (reduce′ j cSplit p₂)
Four' {rSplit = rSplit} {cSplit = cSplit} A B C D i j | yes p₁ | no ¬p₂ = B (reduce′ i rSplit p₁) (reduce″ j cSplit ¬p₂)
Four' {rSplit = rSplit} {cSplit = cSplit} A B C D i j | no ¬p₁ | yes p₂ = C (reduce″ i rSplit ¬p₁) (reduce′ j cSplit p₂)
Four' {rSplit = rSplit} {cSplit = cSplit} A B C D i j | no ¬p₁ | no ¬p₂ = D (reduce″ i rSplit ¬p₁) (reduce″ j cSplit ¬p₂)



-- Extractions
UL : ∀ {m n} → Matrix m n → (rMax : Fin m) → (cMax : Fin n) → Matrix (toℕ rMax) (toℕ cMax)
UL A rMax cMax i j = A (inject i) (inject j)

UR : ∀ {m n} → Matrix m n → (rMax : Fin m) → (cMin : Fin (suc n)) → Matrix (toℕ rMax) (n ℕ-ℕ cMin)
UR A rMax cMin i j = A (inject i) (injectF+F cMin j)
LL : {m n : _} → Matrix m n → (rMin : Fin (suc m)) → (cMax : Fin n) → Matrix (m ℕ-ℕ rMin) (toℕ cMax)
LL A rMin cMax i j = A (injectF+F rMin i) (inject j)

LR : {m n : _} → Matrix m n → (rMin : Fin (suc m)) → (cMin : Fin (suc n)) → Matrix (m ℕ-ℕ rMin) (n ℕ-ℕ cMin)
LR A rMin cMin i j = A (injectF+F rMin i) (injectF+F cMin j)
