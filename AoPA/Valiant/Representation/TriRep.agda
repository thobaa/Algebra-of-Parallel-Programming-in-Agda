open import Valiant.Abstract.NonAssociativeNonRing
open import Valiant.Abstract.NonAssociativeNonRing.Isomorphism
open import Function.Bijection
open import Function.Surjection
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
import Valiant.Concrete.Tri.Zeros

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
open Valiant.Concrete.Tri.Zeros NAR renaming (*-zeroʳ to m*-zeroʳ; *-zeroˡ to m*-zeroˡ)

-- here we prove that if s : Splitting has splitsize n : ℕ, then Tri s ≈ Triangle n

open NonAssociativeNonRing NAR renaming (_+_ to _R+_; _*_ to _R*_; zero to R-zero; refl to R-refl; sym to R-sym; +-identity to R+-identity)
--open NonAssociativeNonRing Mat-nonAssociativeNonRing using () renaming (zero to M-zero) 
--open NonAssociativeNonRing Triangle-nonAssociativeNonRing renaming (_≈_ to _T≈_; refl to T-refl)
--open NonAssociativeNonRing Tri-nonAssociativeNonRing renaming (_≈_ to _t≈_; refl to t-refl)


Tri-to-Triangle : {s : Splitting} {n : ℕ} → splitSize s ≡ n → Tri s → Triangle n
Tri-to-Triangle ≡-refl one = record { matrix = zeroMatrix; proof = λ i j x → R-refl }
Tri-to-Triangle ≡-refl (two U R L) = Three (Tri-to-Triangle ≡-refl U) (Mat-to-Matrix ≡-refl ≡-refl R) (Tri-to-Triangle ≡-refl L)

remove-zero-l : {s₁ s₂ s₃ : Splitting} → (A : Mat s₁ s₂) → (B : Mat s₁ s₃) → A m+ B m* zeroMat m≈ A
remove-zero-l A B = {!m*-zeroʳ B!}
--  where open EqR m-setoid


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


Tri-to-Mat : {s : Splitting} → Tri s → Mat s s
Tri-to-Mat Valiant.Concrete.Tri.one = Valiant.Concrete.Mat.Sing 0#
Tri-to-Mat (Valiant.Concrete.Tri.two U R L) = quad (Tri-to-Mat U) R zeroMat (Tri-to-Mat L)

to-Matrix-equal : {s : Splitting} {n : ℕ} → (|s|≡n : splitSize s ≡ n) → (T : Tri s) → Triangle.matrix (Tri-to-Triangle |s|≡n T) M≈ Mat-to-Matrix |s|≡n |s|≡n (Tri-to-Mat T)
to-Matrix-equal ≡-refl Valiant.Concrete.Tri.one Data.Fin.zero Data.Fin.zero = R-refl
to-Matrix-equal ≡-refl Valiant.Concrete.Tri.one Data.Fin.zero (Data.Fin.suc ())
to-Matrix-equal ≡-refl Valiant.Concrete.Tri.one (Data.Fin.suc ()) _
to-Matrix-equal {deeper s₁ s₂} ≡-refl (Valiant.Concrete.Tri.two U R L) i j with suc (toℕ i) ≤? splitSize s₁ | suc (toℕ j) ≤? splitSize s₁ 
to-Matrix-equal {deeper s₁ s₂} ≡-refl (Valiant.Concrete.Tri.two U R L) i j | yes p | yes p' = to-Matrix-equal ≡-refl U (fromℕ≤ p) (fromℕ≤ p')
to-Matrix-equal {deeper s₁ s₂} ≡-refl (Valiant.Concrete.Tri.two U R L) i j | yes p | no ¬p = R-refl
to-Matrix-equal {deeper s₁ s₂} ≡-refl (Valiant.Concrete.Tri.two U R L) i j | no ¬p | yes p = R-sym (M0-Preserved {s₂} {s₁} ≡-refl ≡-refl (reduce≥ i (≤-pred (≰⇒> ¬p))) (fromℕ≤ p))
to-Matrix-equal {deeper s₁ s₂} ≡-refl (Valiant.Concrete.Tri.two U R L) i j | no ¬p | no ¬p' = to-Matrix-equal ≡-refl L (reduce≥ i (≤-pred (≰⇒> ¬p))) (reduce≥ j (≤-pred (≰⇒> ¬p')))

*-to-Mat-Hom : {s : Splitting} → (x y : Tri s) → Tri-to-Mat (x ◂ y) m≈ Tri-to-Mat x m* Tri-to-Mat y
*-to-Mat-Hom Valiant.Concrete.Tri.one Valiant.Concrete.Tri.one = Sing-eq (R-sym (proj₁ R-zero 0#))
*-to-Mat-Hom (Valiant.Concrete.Tri.two U R L) (Valiant.Concrete.Tri.two U' R' L') = quad-eq {!*-to-Mat-Hom!} {!!} {!M-zero!} {!!}

H : {s : Splitting} {n : ℕ} (|s|≡n : splitSize s ≡ n) → (x y : Tri s) (i j : Fin n) → Triangle.matrix (Tri-to-Triangle |s|≡n (x ◂ y)) i j ≈ (Triangle.matrix (Tri-to-Triangle |s|≡n x) i) ∙ (λ k → Triangle.matrix (Tri-to-Triangle |s|≡n y) k j)
H sn T T' i j = {!!}
*-Homomorphism : {s : Splitting} {n : ℕ} (|s|≡n : splitSize s ≡ n) → (x y : Tri s) (i j : Fin n) → Triangle.matrix (Tri-to-Triangle |s|≡n (x ◂ y)) i j ≈ (Triangle.matrix (Tri-to-Triangle |s|≡n x) i) ∙ (λ k → Triangle.matrix (Tri-to-Triangle |s|≡n y) k j)
*-Homomorphism {one} ≡-refl Valiant.Concrete.Tri.one Valiant.Concrete.Tri.one i j = R-sym (begin 
  0# R* 0# R+ 0# 
    ≈⟨ proj₂ R+-identity (0# R* 0#) ⟩ 
  0# R* 0#
    ≈⟨ proj₁ R-zero 0# ⟩ 
  0# ∎)
  where open EqR setoid
*-Homomorphism {deeper s₁ s₂} ≡-refl (Valiant.Concrete.Tri.two U R L) (Valiant.Concrete.Tri.two U' R' L') i j = begin 
  Four (Triangle.matrix (Tri-to-Triangle ≡-refl (U ◂ U')))
    (Mat-to-Matrix ≡-refl ≡-refl (U ◂* R' m+ R *◂ L')) (λ i' j' → 0#)
    (Triangle.matrix (Tri-to-Triangle ≡-refl (L ◂ L'))) i j 
    ≈⟨ Four-cong (to-Matrix-equal ≡-refl (U ◂ U')) (λ i' j' → R-refl) (λ i' j' → R-refl) (to-Matrix-equal ≡-refl (L ◂ L')) i j ⟩ 
  Four (Mat-to-Matrix ≡-refl ≡-refl (Tri-to-Mat (U ◂ U'))) (Mat-to-Matrix ≡-refl ≡-refl (U ◂* R' m+ R *◂ L')) zeroMatrix (Mat-to-Matrix ≡-refl ≡-refl (Tri-to-Mat (L ◂ L'))) i j 
    ≈⟨ {!!} ⟩
  Four (Mat-to-Matrix ≡-refl ≡-refl (Tri-to-Mat U m* Tri-to-Mat U'))
    (Mat-to-Matrix ≡-refl ≡-refl (U ◂* R' m+ R *◂ L')) zeroMatrix
    (Mat-to-Matrix ≡-refl ≡-refl (Tri-to-Mat L m* Tri-to-Mat L')) i j
    ≈⟨ {!!} ⟩
  row i
    (Four (Triangle.matrix (Tri-to-Triangle ≡-refl U))
     (Mat-to-Matrix ≡-refl ≡-refl R) 
     (λ i' j0 → 0#)
     (Triangle.matrix (Tri-to-Triangle ≡-refl L)))
    ∙
    col j
    (Four
     (Triangle.matrix (Tri-to-Triangle ≡-refl U'))
     (Mat-to-Matrix ≡-refl ≡-refl R') 
     (λ i' j' → 0#)
     (Triangle.matrix (Tri-to-Triangle ≡-refl L'))) ∎
  where open EqR setoid

{-with suc (toℕ i) ≤? splitSize s₁ | suc (toℕ j) ≤? splitSize s₁
*-Homomorphism {deeper s₁ s₂} ≡-refl (Valiant.Concrete.Tri.two U R L) (Valiant.Concrete.Tri.two U' R' L') i j | yes p | yes p' = begin 
  Triangle.matrix (Tri-to-Triangle ≡-refl (U ◂ U')) (fromℕ≤ p) (fromℕ≤ p') 
    ≈⟨ *-Homomorphism ≡-refl U U' (fromℕ≤ p) (fromℕ≤ p') ⟩
  Triangle.matrix (Tri-to-Triangle ≡-refl U) (fromℕ≤ p) ∙ (λ k → Triangle.matrix (Tri-to-Triangle ≡-refl U') k (fromℕ≤ p'))
    ≈⟨ {!!} ⟩ --M*-Homomorphism ≡-refl ≡-refl ≡-refl {!!} {!!} {!!} {!!} ⟩
  _ ∎
  where open EqR setoid
*-Homomorphism {deeper s₁ s₂} ≡-refl (Valiant.Concrete.Tri.two U R L) (Valiant.Concrete.Tri.two U' R' L') i j | yes p | no ¬p = {!!}
*-Homomorphism {deeper s₁ s₂} ≡-refl (Valiant.Concrete.Tri.two U R L) (Valiant.Concrete.Tri.two U' R' L') i j | no ¬p | yes p = {!!}
*-Homomorphism {deeper s₁ s₂} ≡-refl (Valiant.Concrete.Tri.two U R L) (Valiant.Concrete.Tri.two U' R' L') i j | no ¬p | no ¬p' = {!!}
  where open EqR setoid

--M0-Preserved : {n : ℕ}{s₁ s₂ : Splitting} {pf : splitSize (deeper s₁ s₂) ≡ n} {i j : Fin n} {p : suc (toℕ i) < splitSize s₁} {¬p : ¬ suc (toℕ j) ≤ splitSize s₁} → Mat-to-Matrix ≡-refl ≡-refl zeroMat (fromℕ≤ p) (reduce≥ j (≤-pred (≰⇒> ¬p))) ≈ 0#
--M0-Preserved = {!!}

-}

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


Tri-Triangle-Injective : (s : Splitting) → (n : ℕ) → (|s|≡n : splitSize s ≡ n) → {x y : Tri s} →
      ((i j : Fin n) →
       Triangle.matrix (Tri-to-Triangle |s|≡n x) i j ≈
       Triangle.matrix (Tri-to-Triangle |s|≡n y) i j) →
      x t≈ y
Tri-Triangle-Injective one .1 ≡-refl {Valiant.Concrete.Tri.one} {Valiant.Concrete.Tri.one} x≈y = Valiant.Concrete.Tri.Equalities.one-eq
Tri-Triangle-Injective (deeper s₁ s₂) .(splitSize s₁ + splitSize s₂) ≡-refl {Valiant.Concrete.Tri.two U R L} {Valiant.Concrete.Tri.two U' R' L'} x≈y = Valiant.Concrete.Tri.Equalities.two-eq (Tri-Triangle-Injective s₁ (splitSize s₁) ≡-refl (M≈-reduce₁ (Triangle.matrix (Tri-to-Triangle ≡-refl U)) (Triangle.matrix (Tri-to-Triangle ≡-refl U')) (Mat-to-Matrix ≡-refl ≡-refl R) (Mat-to-Matrix ≡-refl ≡-refl R') (λ i' j' → 0#) (λ i' j' → 0#) (Triangle.matrix (Tri-to-Triangle ≡-refl L)) (Triangle.matrix (Tri-to-Triangle ≡-refl L')) x≈y)) {!!} (Tri-Triangle-Injective s₂ (splitSize s₂) ≡-refl {!(M≈-reduce₄ (Triangle.matrix (Tri-to-Triangle ≡-refl U)) (Triangle.matrix (Tri-to-Triangle ≡-refl U')) (Mat-to-Matrix ≡-refl ≡-refl R) (Mat-to-Matrix ≡-refl ≡-refl R') (λ i' j' → 0#) (λ i' j' → 0#) (Triangle.matrix (Tri-to-Triangle ≡-refl L)) (Triangle.matrix (Tri-to-Triangle ≡-refl L')) x≈y)!})

Tri-Triangle-Surjective : (s : Splitting) → (n : ℕ) → (|s|≡n : splitSize s ≡ n) → Surjective
      (record {
       _⟨$⟩_ = Tri-to-Triangle {s} |s|≡n;
       cong = Tri-to-Triangle-cong |s|≡n })
Tri-Triangle-Surjective = {!!}
Tri-Triangle-Bijective : (s : Splitting) → (n : ℕ) → (|s|≡n : splitSize s ≡ n) → Bijective (record { _⟨$⟩_ = Tri-to-Triangle |s|≡n; cong = Tri-to-Triangle-cong |s|≡n })
Tri-Triangle-Bijective s n |s|≡n = record { injective = Tri-Triangle-Injective s n |s|≡n; surjective = Tri-Triangle-Surjective s n |s|≡n }

Tri-Triangle-Isomorphism : (s : Splitting) → (n : ℕ) → splitSize s ≡ n → NANRing-Isomorphism (Tri-nonAssociativeNonRing {s}) (Triangle-nonAssociativeNonRing {n})
Tri-Triangle-Isomorphism s n |s|≡n = record 
  { homomorphism = Tri-Triangle-Homomorphism s n |s|≡n
  ; bijective = Tri-Triangle-Bijective s n |s|≡n --Tri-Triangle-Bijection s n |s|≡n 
  }