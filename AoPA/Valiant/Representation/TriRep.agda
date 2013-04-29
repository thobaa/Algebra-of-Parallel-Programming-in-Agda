open import Valiant.Abstract.NonAssociativeNonRing
open import Valiant.Abstract.NonAssociativeNonRing.Isomorphism
open import Valiant.Concrete.Splitting
open import Data.Nat using (ℕ; _+_; suc; zero; _≤?_; ≤-pred; _≤_; _<_)
open import Data.Nat.Properties using (≰⇒>)
open import Data.Fin using (Fin; toℕ; fromℕ≤; reduce≥)
open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to ≡-refl)
import Relation.Binary.EqReasoning as EqR 
open import Relation.Nullary -- using (yes; no)
open import Data.Product using (proj₁; proj₂)


module Valiant.Representation.TriRep {l₁ l₂} (NAR : NonAssociativeNonRing l₁ l₂) where

import Valiant.Abstract.Triangle
import Valiant.Abstract.Matrix
import Valiant.Abstract.Matrix.Operations
import Valiant.Representation.MatRep
import Valiant.Abstract.Triangle.NANRing
import Valiant.Concrete.Tri
import Valiant.Concrete.Tri.Properties
import Valiant.Concrete.Mat
import Valiant.Concrete.Mat.Operations
import Valiant.Concrete.Tri.Equalities
import Valiant.Concrete.Tri.Operations

open Valiant.Abstract.Triangle NAR
open Valiant.Abstract.Matrix NAR
open Valiant.Abstract.Matrix.Operations NAR renaming (_+_ to _M+_; _*_ to _M*_)
open Valiant.Representation.MatRep NAR
open Valiant.Abstract.Triangle.NANRing NAR renaming (nonAssociativeNonRing to Triangle-nonAssociativeNonRing)
open Valiant.Concrete.Tri NAR
open Valiant.Concrete.Tri.Properties NAR renaming (nonAssociativeNonRing to Tri-nonAssociativeNonRing)
open Valiant.Concrete.Tri.Equalities NAR
open Valiant.Concrete.Mat NAR
open Valiant.Concrete.Mat.Operations NAR renaming (_+_ to _m+_; _*_ to _m*_; _∙_ to _m∙_)
open Valiant.Concrete.Tri.Operations NAR

-- here we prove that if s : Splitting has splitsize n : ℕ, then Tri s ≈ Triangle n

open NonAssociativeNonRing NAR renaming (_+_ to _R+_; _*_ to _R*_; zero to R-zero; refl to R-refl; sym to R-sym; +-identity to R+-identity)
--open NonAssociativeNonRing Triangle-nonAssociativeNonRing renaming (_≈_ to _T≈_; refl to T-refl)
--open NonAssociativeNonRing Tri-nonAssociativeNonRing renaming (_≈_ to _t≈_; refl to t-refl)

Tri-to-Triangle : {s : Splitting} {n : ℕ} → splitSize s ≡ n → Tri s → Triangle n
Tri-to-Triangle ≡-refl one = record { matrix = zeroMatrix; proof = λ i j x → R-refl }
Tri-to-Triangle ≡-refl (two U R L) = Three (Tri-to-Triangle ≡-refl U) (Mat-to-Matrix ≡-refl ≡-refl R) (Tri-to-Triangle ≡-refl L)



Tri-to-Triangle-cong : {s : Splitting} {n : ℕ} → 
                       let _t≈_ = NonAssociativeNonRing._≈_ (Tri-nonAssociativeNonRing {s}) 
                           _T≈_ = NonAssociativeNonRing._≈_ (Triangle-nonAssociativeNonRing {n}) 
                       in {i j : Tri s} → (|s|≡n : splitSize s ≡ n) → 
                         i t≈ j → Tri-to-Triangle |s|≡n i T≈ Tri-to-Triangle |s|≡n j
Tri-to-Triangle-cong {one} {.(suc zero)} {Valiant.Concrete.Tri.one} {Valiant.Concrete.Tri.one} ≡-refl i=j i j = R-refl
Tri-to-Triangle-cong {(deeper s₁ s₂)} {.(splitSize s₁ + splitSize s₂)} {Valiant.Concrete.Tri.two U R L} {Valiant.Concrete.Tri.two U' R' L'} ≡-refl i=j i j with suc (toℕ i) ≤? splitSize s₁ | suc (toℕ j) ≤? splitSize s₁
Tri-to-Triangle-cong {deeper s₁ s₂} {.(splitSize s₁ + splitSize s₂)} {Valiant.Concrete.Tri.two U R L} {Valiant.Concrete.Tri.two U' R' L'} ≡-refl (two-eq U₁≈U₂ R₁≈R₂ L₁≈L₂) i j | yes p | yes p' = Tri-to-Triangle-cong {s₁} {splitSize s₁} {U} {U'} ≡-refl U₁≈U₂ (fromℕ≤ p) (fromℕ≤ p')
Tri-to-Triangle-cong {deeper s₁ s₂} {.(splitSize s₁ + splitSize s₂)} {Valiant.Concrete.Tri.two U R L} {Valiant.Concrete.Tri.two U' R' L'} ≡-refl (two-eq U₁≈U₂ R₁≈R₂ L₁≈L₂) i j | yes p | no ¬p = Mat-to-Matrix-cong {s₁} {s₂} ≡-refl ≡-refl R₁≈R₂ (fromℕ≤ p) (reduce≥ j (≤-pred (≰⇒> ¬p))) -- Mat-to-Matrix-cong {s₁} {s₂} ≡-refl ≡-refl {!R₁≈R₂!} {!!} {!!}
Tri-to-Triangle-cong {deeper s₁ s₂} {.(splitSize s₁ + splitSize s₂)} {Valiant.Concrete.Tri.two U R L} {Valiant.Concrete.Tri.two U' R' L'} ≡-refl (two-eq U₁≈U₂ R₁≈R₂ L₁≈L₂) i j | no ¬p | yes p = R-refl
Tri-to-Triangle-cong {deeper s₁ s₂} {.(splitSize s₁ + splitSize s₂)} {Valiant.Concrete.Tri.two U R L} {Valiant.Concrete.Tri.two U' R' L'} ≡-refl (two-eq U₁≈U₂ R₁≈R₂ L₁≈L₂) i j | no ¬p | no ¬p' = Tri-to-Triangle-cong {s₂} {splitSize s₂} {L} {L'} ≡-refl L₁≈L₂ (reduce≥ i (≤-pred (≰⇒> ¬p))) (reduce≥ j (≤-pred (≰⇒> ¬p')))

+-Homomorphism : {s : Splitting} {n : ℕ} (|s|≡n : splitSize s ≡ n) → (x y : Tri s) (i j : Fin n) →
      Triangle.matrix
      (Tri-to-Triangle |s|≡n
       (x ◂+ y))
      i j
      ≈
      Triangle.matrix (Tri-to-Triangle |s|≡n x) i j R+
      Triangle.matrix (Tri-to-Triangle |s|≡n y) i j
+-Homomorphism {one} ≡-refl one one i j = R-sym (proj₁ R+-identity 0#)
+-Homomorphism {deeper s₁ s₂} ≡-refl (Valiant.Concrete.Tri.two U R L) (Valiant.Concrete.Tri.two U' R' L') i j with suc (toℕ i) ≤? splitSize s₁ | suc (toℕ j) ≤? splitSize s₁ 
+-Homomorphism {deeper s₁ s₂} ≡-refl (Valiant.Concrete.Tri.two U R L) (Valiant.Concrete.Tri.two U' R' L') i j | yes p | yes p' = +-Homomorphism ≡-refl U U' (fromℕ≤ p) (fromℕ≤ p')
+-Homomorphism {deeper s₁ s₂} ≡-refl (Valiant.Concrete.Tri.two U R L) (Valiant.Concrete.Tri.two U' R' L') i j | yes p | no ¬p = M+-Homomorphism ≡-refl ≡-refl R R' (fromℕ≤ p) (reduce≥ j (≤-pred (≰⇒> ¬p)))
+-Homomorphism {deeper s₁ s₂} ≡-refl (Valiant.Concrete.Tri.two U R L) (Valiant.Concrete.Tri.two U' R' L') i j | no ¬p | yes p = R-sym (proj₁ R+-identity 0#)
+-Homomorphism {deeper s₁ s₂} ≡-refl (Valiant.Concrete.Tri.two U R L) (Valiant.Concrete.Tri.two U' R' L') i j | no ¬p | no ¬p' = +-Homomorphism ≡-refl L L' (reduce≥ i (≤-pred (≰⇒> ¬p))) (reduce≥ j (≤-pred (≰⇒> ¬p')))

-- something about dot-product
--Goal: Triangle.matrix (Tri-to-Triangle ≡-refl (L ◂ L'))
--      (reduce≥ i (≤-pred (≰⇒> ¬p))) (reduce≥ j (≤-pred (≰⇒> ¬p')))
--      ≈
--      (λ j' →
--         Valiant.Abstract.Matrix.Four NAR
--         (Triangle.matrix (Tri-to-Triangle ≡-refl U))
--         (Mat-to-Matrix ≡-refl ≡-refl R) (λ i' j0 → 0#)
--         (Triangle.matrix (Tri-to-Triangle ≡-refl L)) i j'
--         | no ¬p | suc (toℕ j') ≤? splitSize s₁)
--      ∙
--      (λ k →
--         Valiant.Abstract.Matrix.Four NAR
--         (Triangle.matrix (Tri-to-Triangle ≡-refl U'))
--         (Mat-to-Matrix ≡-refl ≡-refl R') (λ i' j' → 0#)
--         (Triangle.matrix (Tri-to-Triangle ≡-refl L')) k j
--         | suc (toℕ k) ≤? splitSize s₁ | no ¬p')

--result : {m n : ℕ} → {A : Matrix m m} {B : Matrix m n} {C : Matrix n m} {D : Matrix n n} {i j : Fin (m + n)} → Carrier
--result = {!!}

--row-col-prod-four : {m n : ℕ} → {A : Matrix m m} {B : Matrix m n} {C : Matrix n m} {D : Matrix n n} {i j : Fin (m + n)} → (λ k → (Four A B C D) i k) ∙ (λ k → Four A B C D k j) ≈ {!!}
--row-col-prod-four = {!!}

-- why doesn't it work to have i j in Fin n₁ n₂



*-Homomorphism : {s : Splitting} {n : ℕ} (|s|≡n : splitSize s ≡ n) → (x y : Tri s) (i j : Fin n) → Triangle.matrix (Tri-to-Triangle |s|≡n (x ◂ y)) i j ≈ (Triangle.matrix (Tri-to-Triangle |s|≡n x) i) ∙ (λ k → Triangle.matrix (Tri-to-Triangle |s|≡n y) k j)
*-Homomorphism {one} ≡-refl Valiant.Concrete.Tri.one Valiant.Concrete.Tri.one i j = R-sym (begin 
  0# R* 0# R+ 0# 
    ≈⟨ proj₂ R+-identity (0# R* 0#) ⟩ 
  0# R* 0#
    ≈⟨ proj₁ R-zero 0# ⟩ 
  0# ∎)
  where open EqR setoid
*-Homomorphism {deeper s₁ s₂} ≡-refl (Valiant.Concrete.Tri.two U R L) (Valiant.Concrete.Tri.two U' R' L') i j with suc (toℕ i) ≤? splitSize s₁ | suc (toℕ j) ≤? splitSize s₁
*-Homomorphism {deeper s₁ s₂} ≡-refl (Valiant.Concrete.Tri.two U R L) (Valiant.Concrete.Tri.two U' R' L') i j | yes p | yes p' = begin 
  Triangle.matrix (Tri-to-Triangle ≡-refl (U ◂ U')) (fromℕ≤ p) (fromℕ≤ p') 
    ≈⟨ *-Homomorphism ≡-refl U U' (fromℕ≤ p) (fromℕ≤ p') ⟩
  Triangle.matrix (Tri-to-Triangle ≡-refl U) (fromℕ≤ p) ∙ (λ k → Triangle.matrix (Tri-to-Triangle ≡-refl U') k (fromℕ≤ p'))
    ≈⟨ {!!} ⟩ -- need triangularity!
  _ ∎
  where open EqR setoid
*-Homomorphism {deeper s₁ s₂} ≡-refl (Valiant.Concrete.Tri.two U R L) (Valiant.Concrete.Tri.two U' R' L') i j | yes p | no ¬p = {!!} --M*-Homomorphism ≡-refl ≡-refl ≡-refl {!R!} {!!} {!!} {!!}
*-Homomorphism {deeper s₁ s₂} ≡-refl (Valiant.Concrete.Tri.two U R L) (Valiant.Concrete.Tri.two U' R' L') i j | no ¬p | yes p = {!!}
*-Homomorphism {deeper s₁ s₂} ≡-refl (Valiant.Concrete.Tri.two U R L) (Valiant.Concrete.Tri.two U' R' L') i j | no ¬p | no ¬p' = {!!}
  where open EqR setoid

--M0-Preserved : {n : ℕ}{s₁ s₂ : Splitting} {pf : splitSize (deeper s₁ s₂) ≡ n} {i j : Fin n} {p : suc (toℕ i) < splitSize s₁} {¬p : ¬ suc (toℕ j) ≤ splitSize s₁} → Mat-to-Matrix ≡-refl ≡-refl zeroMat (fromℕ≤ p) (reduce≥ j (≤-pred (≰⇒> ¬p))) ≈ 0#
--M0-Preserved = {!!}



abstract 
  0-Preserved : {s : Splitting} {n : ℕ} (|s|≡n : splitSize s ≡ n) → (i j : Fin n) →
      Triangle.matrix (Tri-to-Triangle |s|≡n (zeroTri {s})) i j ≈ 0#
  0-Preserved {one} ≡-refl i j = R-refl
  0-Preserved {deeper s₁ s₂} ≡-refl i j with suc (toℕ i) ≤? splitSize s₁ | suc (toℕ j) ≤? splitSize s₁
  0-Preserved {deeper s₁ s₂} ≡-refl i j | yes p | yes p' = 0-Preserved {s₁} ≡-refl (fromℕ≤ p) (fromℕ≤ p')
  0-Preserved {deeper s₁ s₂} ≡-refl i j | yes p | no ¬p = M0-Preserved {s₁} {s₂} ≡-refl ≡-refl (fromℕ≤ p) (reduce≥ j (≤-pred (≰⇒> ¬p)))
  0-Preserved {deeper s₁ s₂} ≡-refl i j | no ¬p | yes p = R-refl
  0-Preserved {deeper s₁ s₂} ≡-refl i j | no ¬p | no ¬p' = 0-Preserved {s₂} ≡-refl (reduce≥ i (≤-pred (≰⇒> ¬p))) (reduce≥ j (≤-pred (≰⇒> ¬p')))

Tri-Triangle-Homomorphism : (s : Splitting) → (n : ℕ) → splitSize s ≡ n → NANRing-Homomorphism (Tri-nonAssociativeNonRing {s}) (Triangle-nonAssociativeNonRing {n})
Tri-Triangle-Homomorphism s n |s|≡n = record 
  { ⟦_⟧ = Tri-to-Triangle |s|≡n
  ; ⟦⟧-cong = Tri-to-Triangle-cong |s|≡n
  ; +-hom = +-Homomorphism |s|≡n
  ; *-hom = *-Homomorphism |s|≡n
  ; 0-hom = 0-Preserved {s} |s|≡n 
  }

Tri-Triangle-Isomorphism : (s : Splitting) → (n : ℕ) → splitSize s ≡ n → NANRing-Isomorphism (Tri-nonAssociativeNonRing {s}) (Triangle-nonAssociativeNonRing {n})
Tri-Triangle-Isomorphism s n |s|≡n = record 
  { homomorphism = Tri-Triangle-Homomorphism s n |s|≡n
  ; bijective = {!!} 
  }