open import Data.Nat
open import Data.Fin using (Fin; fromℕ; fromℕ≤; toℕ;  raise; reduce≥) 
                     renaming (zero to f0; suc to fsuc)
open import Data.Nat.Properties using (≰⇒>)
open import Data.Product using (proj₁; proj₂)
open import Data.Empty


open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to ≡-refl; cong to ≡-cong; cong₂ to ≡-cong₂)
open Relation.Binary.PropositionalEquality.Deprecated-inspect

import Relation.Binary.EqReasoning as EqR
open import Relation.Nullary
open import Relation.Nullary.Decidable

open import Valiant.Abstract.NonAssociativeNonRing
open import Valiant.Concrete.Splitting
module Valiant.Representation.MatRep {l₁ l₂} (NAR : NonAssociativeNonRing l₁ l₂) where

import Valiant.Helper.Definitions
import Valiant.Concrete.Mat
import Valiant.Concrete.Mat.Operations
import Valiant.Abstract.Matrix
import Valiant.Abstract.Matrix.Operations
import Valiant.Concrete.Tri.Equalities

open Valiant.Helper.Definitions NAR using ()
open Valiant.Concrete.Mat NAR
open Valiant.Concrete.Mat.Operations NAR using (_|⊛_; _⊛|_; _|*_; _*|_; _v≈_; _m≈_; Sing-eq; one-eq; two-eq; CVec-eq; RVec-eq; quad-eq) renaming (_+_ to _m+_; _*_ to _m*_; _⊕_ to _v+_; _∙_ to _v∙_; _⊛_ to _v⊗_)
open Valiant.Abstract.Matrix NAR

open Valiant.Abstract.Matrix.Operations NAR using (_M≈_; _V≈_; _V+_; _Vs*_; _sV*_; _MV*_; _VM*_; trans-∙) renaming (_+_ to _M+_;_*_ to _M*_; _∙_ to _V∙_; _⊗_ to _V⊗_)
--open Valiant.Concrete.Tri.Equalities NAR using (_m≈_; _v≈_)


open NonAssociativeNonRing NAR renaming (_+_ to _R+_; _*_ to _R*_; zero to R-zero; refl to R-refl; sym to R-sym; +-identity to R+-identity; +-cong to R+-cong; +-assoc to R+-assoc; *-cong to R*-cong)
{-
-- vector stuff
projVec : ∀ {s} → Vec s → Vector (splitSize s)
projVec (one x) = λ i → x
projVec (two y y') = V++ (projVec y) (projVec y')

projVec' : ∀ {m} → Vec (simpleSplit m) → Vector (suc m)
projVec' {zero} (one x) = λ i → x
projVec' {suc n} (two v₁  v₂) = V++ (projVec' v₁) (projVec' v₂)

vecToRMat : ∀ {n} → Vector n → Matrix 1 n
vecToRMat v = λ i j → v j

vecToCMat : ∀ {n} → Vector n → Matrix n 1
vecToCMat v = λ i j → v i

embedVec : ∀ {n} → Vector (suc n) → Vec (simpleSplit n)
embedVec {zero} v = one (v f0)
embedVec {suc n} v = two (one (v f0)) (embedVec (λ x → v (fsuc x)))


-}
-- these are new!
Vec-to-Vector : {s : Splitting} {n : ℕ} → (|s|≡n : splitSize s ≡ n) → Vec s → Vector n
Vec-to-Vector {one} ≡-refl (one x) f0 = x
Vec-to-Vector {one} ≡-refl (one x) (fsuc ())
Vec-to-Vector {deeper s₁ s₂} ≡-refl (two u v) i = Two (Vec-to-Vector ≡-refl u) (Vec-to-Vector ≡-refl v) i

Mat-to-Matrix : {s₁ s₂ : Splitting} {n₁ n₂ : ℕ} → (splitSize s₁ ≡ n₁) → (splitSize s₂ ≡ n₂) → Mat s₁ s₂ → Matrix n₁ n₂
Mat-to-Matrix {one} {one} ≡-refl ≡-refl (Sing x) f0 f0 = x
Mat-to-Matrix {one} {one} ≡-refl ≡-refl A f0 (fsuc ())
Mat-to-Matrix {one} {one} ≡-refl ≡-refl A (fsuc ()) _
Mat-to-Matrix {deeper s₁ s₂} {one} ≡-refl ≡-refl (CVec v) i f0 = Vec-to-Vector ≡-refl v i
Mat-to-Matrix {deeper s₁ s₂} {one} ≡-refl ≡-refl A i (fsuc ())
Mat-to-Matrix {one} {deeper s₁' s₂} ≡-refl ≡-refl (RVec v) f0 j = Vec-to-Vector ≡-refl v j
Mat-to-Matrix {one} {deeper s₁' s₂} ≡-refl ≡-refl A (fsuc ()) j
Mat-to-Matrix {deeper s₁ s₂} {deeper s₁' s₂'} ≡-refl ≡-refl (quad A B C D) i j = Four (Mat-to-Matrix ≡-refl ≡-refl A) (Mat-to-Matrix ≡-refl ≡-refl B) (Mat-to-Matrix ≡-refl ≡-refl C) (Mat-to-Matrix ≡-refl ≡-refl D) i j

-- the way we have it is: matToSplit: tar en matris till en konkret.
-- typ lista -> tree, den viktika delen är att vilket träd som helst kan formas
-- om till en lista. inte så viktigt att 
-- 
{-
splitToMat : ∀ {s₁ s₂} → Mat s₁ s₂ → Matrix (splitSize s₁) (splitSize s₂)
{-splitToMat {zero} {zero} (Sing x) = λ i j → x
splitToMat {suc n} {zero} (CVec y) = {!!}
splitToMat {zero} {suc n} (RVec y) = {!!}
splitToMat {suc n} {suc n'} (quad A B 
                                  C D) = Four (splitToMat A) (splitToMat B) 
                                              (splitToMat C) (splitToMat D)
-}
splitToMat {one} {one} (Sing x) = λ _ _ → x 
splitToMat {deeper y y'} {one} (CVec y0) = vecToCMat (projVec y0)
splitToMat {one} {deeper y y'} (RVec y0) = vecToRMat (projVec y0)
splitToMat {deeper y y'} {deeper y0 y1} (quad A B 
                                                C D) = Four (splitToMat A) (splitToMat B) 
                                                            (splitToMat C) (splitToMat D)

-}
-- should not be this way.???
-- nej. vi har inte en metod som skapar element av godtyckliga splittar.
--matToSplit : ∀ {s₁ s₂} → Matrix (splitSize s₁) (splitSize s₂) → Mat s₁ s₂
--matToSplit = {!!}

-- behöver en relation mellan alla 
-- splitToMat : ∀ {m n} → Mat 


-- i matrepproofs finns satsen vi vill ha.
{-
matToSplit {zero} {zero} mat = Sing (mat f0 f0)
matToSplit {suc n} {zero} mat = CVec (embedVec (λ x → mat x f0))
matToSplit {zero} {suc n} mat = RVec (embedVec (λ x → mat f0 x))
matToSplit {suc zero} {suc zero} mat = quad (Sing (mat f0 f0)) (Sing (mat f0 f1)) 
                                              (Sing (mat f1 f0)) (Sing (mat f1 f1))
matToSplit {suc zero} {suc (suc n)} mat = quad (Sing (mat f0 f0)) (RVec (embedVec (λ x → mat f0 (fsuc x)))) (Sing (mat f1 f0)) (RVec (embedVec (λ x → mat f1 (fsuc x))))
matToSplit {suc (suc n)} {suc zero} mat = quad (Sing (mat f0 f0)) (Sing (mat f0 f1)) (CVec (embedVec (λ x → mat (fsuc x) f0))) (CVec (embedVec (λ x → mat (fsuc x) f1)))
matToSplit {suc (suc n)} {suc (suc n')} mat = quad (Sing (mat f0 f0)) (RVec (embedVec (λ x → mat f0 (fsuc x)))) (CVec (embedVec (λ x → mat (fsuc x) f0))) (matToSplit (λ x x' → mat (fsuc x) (fsuc x')))
-}
abstract
  V0-Preserved : {s : Splitting} {n : ℕ} (|s|≡n : splitSize s ≡ n) → (i : Fin n) → Vec-to-Vector |s|≡n (zeroVec {s}) i ≈ 0#
  V0-Preserved {one} ≡-refl f0 = R-refl
  V0-Preserved {one} ≡-refl (fsuc ())
  V0-Preserved {deeper s₁ s₂} ≡-refl i with suc (toℕ i) ≤? splitSize s₁
  V0-Preserved {deeper s₁ s₂} ≡-refl i | yes p = V0-Preserved {s₁} ≡-refl (fromℕ≤ p)
  V0-Preserved {deeper s₁ s₂} ≡-refl i | no ¬p = V0-Preserved {s₂} ≡-refl (reduce≥ i (≤-pred (≰⇒> ¬p)))
  M0-Preserved : {s₁ s₂ : Splitting} {n₁ n₂ : ℕ} (|s₁|≡n₁ : splitSize s₁ ≡ n₁) (|s₂|≡n₂ : splitSize s₂ ≡ n₂)  → (i : Fin n₁) (j : Fin n₂) →
               Mat-to-Matrix |s₁|≡n₁ |s₂|≡n₂ (zeroMat {s₁} {s₂}) i j ≈ 0#
  M0-Preserved {one} {one} ≡-refl ≡-refl Data.Fin.zero Data.Fin.zero = R-refl
  M0-Preserved {one} {one} ≡-refl ≡-refl Data.Fin.zero (Data.Fin.suc ())
  M0-Preserved {one} {one} ≡-refl ≡-refl (Data.Fin.suc ()) j
  M0-Preserved {deeper s₁ s₂} {one} ≡-refl ≡-refl i f0 = V0-Preserved {deeper s₁ s₂} ≡-refl i
  M0-Preserved {deeper s₁ s₂} {one} ≡-refl ≡-refl i (fsuc ()) --V0-Preserved ≡-refl i
  M0-Preserved {one} {deeper s₁ s₂} ≡-refl ≡-refl f0 j = V0-Preserved {deeper s₁ s₂} ≡-refl j
  M0-Preserved {one} {deeper s₁ s₂} ≡-refl ≡-refl (fsuc ()) j
  M0-Preserved {deeper s₁ s₂} {deeper s₁' s₂'} ≡-refl ≡-refl i j with suc (toℕ i) ≤? splitSize s₁ | suc (toℕ j) ≤? splitSize s₁' 
  M0-Preserved {deeper s₁ s₂} {deeper s₁' s₂'} ≡-refl ≡-refl i j | yes p | yes p' = M0-Preserved {s₁} {s₁'} ≡-refl ≡-refl (fromℕ≤ p) (fromℕ≤ p')
  M0-Preserved {deeper s₁ s₂} {deeper s₁' s₂'} ≡-refl ≡-refl i j | yes p | no ¬p = M0-Preserved {s₁} {s₂'} ≡-refl ≡-refl (fromℕ≤ p) (reduce≥ j (≤-pred (≰⇒> ¬p)))
  M0-Preserved {deeper s₁ s₂} {deeper s₁' s₂'} ≡-refl ≡-refl i j | no ¬p | yes p = M0-Preserved {s₂} {s₁'} ≡-refl ≡-refl (reduce≥ i (≤-pred (≰⇒> ¬p))) (fromℕ≤ p)
  M0-Preserved {deeper s₁ s₂} {deeper s₁' s₂'} ≡-refl ≡-refl i j | no ¬p | no ¬p' = M0-Preserved {s₂} {s₂'} ≡-refl ≡-refl (reduce≥ i (≤-pred (≰⇒> ¬p))) (reduce≥ j (≤-pred (≰⇒> ¬p')))

  Vec-to-Vector-cong : {s : Splitting} {n : ℕ} → {u v : Vec s} → (|s|≡n : splitSize s ≡ n) → u v≈ v → Vec-to-Vector |s|≡n u V≈ Vec-to-Vector |s|≡n v 
  Vec-to-Vector-cong {one} ≡-refl (one-eq x≈y) f0 = x≈y
  Vec-to-Vector-cong {one} ≡-refl (one-eq x≈y) (fsuc ())
  Vec-to-Vector-cong {deeper s₁ s₂} ≡-refl (two-eq u₁≈v₁ u₂≈v₂) i with suc (toℕ i) ≤? splitSize s₁
  Vec-to-Vector-cong {deeper s₁ s₂} ≡-refl (two-eq u₁≈v₁ u₂≈v₂) i | yes p = Vec-to-Vector-cong ≡-refl u₁≈v₁ (fromℕ≤ p)
  Vec-to-Vector-cong {deeper s₁ s₂} ≡-refl (two-eq u₁≈v₁ u₂≈v₂) i | no ¬p = Vec-to-Vector-cong ≡-refl u₂≈v₂ (reduce≥ i (≤-pred (≰⇒> ¬p)))


  Mat-to-Matrix-cong : {s₁ s₂ : Splitting} {n₁ n₂ : ℕ} → 
                       {A B : Mat s₁ s₂} → (|s₁|≡n₁ : splitSize s₁ ≡ n₁) → (|s₂|≡n₂ : splitSize s₂ ≡ n₂) → 
                          A m≈ B → Mat-to-Matrix |s₁|≡n₁ |s₂|≡n₂ A M≈ Mat-to-Matrix |s₁|≡n₁ |s₂|≡n₂ B
  Mat-to-Matrix-cong {one} {one} ≡-refl ≡-refl (Sing-eq x≈y) f0 f0 = x≈y
  Mat-to-Matrix-cong {one} {one} ≡-refl ≡-refl (Sing-eq x≈y) f0 (fsuc ())
  Mat-to-Matrix-cong {one} {one} ≡-refl ≡-refl (Sing-eq x≈y) (fsuc ()) j
  Mat-to-Matrix-cong {deeper s₁ s₂} {one} ≡-refl ≡-refl (CVec-eq u≈v) i f0 = Vec-to-Vector-cong ≡-refl u≈v i
  Mat-to-Matrix-cong {deeper s₁ s₂} {one} ≡-refl ≡-refl (CVec-eq u≈v) i (fsuc ())
  Mat-to-Matrix-cong {one} {deeper s₁' s₂} ≡-refl ≡-refl (RVec-eq u≈v) f0 j = Vec-to-Vector-cong ≡-refl u≈v j
  Mat-to-Matrix-cong {one} {deeper s₁' s₂} ≡-refl ≡-refl (RVec-eq u≈v) (fsuc ()) j
  Mat-to-Matrix-cong {deeper s₁ s₂} {deeper s₁' s₂'} ≡-refl ≡-refl (quad-eq A₁≈A₂ B₁≈B₂ C₁≈C₂ D₁≈D₂) i j with suc (toℕ i) ≤? splitSize s₁ | suc (toℕ j) ≤? splitSize s₁'
  Mat-to-Matrix-cong {deeper s₁ s₂} {deeper s₁' s₂'} ≡-refl ≡-refl (quad-eq A₁≈A₂ B₁≈B₂ C₁≈C₂ D₁≈D₂) i j | yes p | yes p' = Mat-to-Matrix-cong ≡-refl ≡-refl A₁≈A₂ (fromℕ≤ p) (fromℕ≤ p')
  Mat-to-Matrix-cong {deeper s₁ s₂} {deeper s₁' s₂'} ≡-refl ≡-refl (quad-eq A₁≈A₂ B₁≈B₂ C₁≈C₂ D₁≈D₂) i j | yes p | no ¬p = Mat-to-Matrix-cong ≡-refl ≡-refl B₁≈B₂ (fromℕ≤ p) (reduce≥ j (≤-pred (≰⇒> ¬p)))
  Mat-to-Matrix-cong {deeper s₁ s₂} {deeper s₁' s₂'} ≡-refl ≡-refl (quad-eq A₁≈A₂ B₁≈B₂ C₁≈C₂ D₁≈D₂) i j | no ¬p | yes p = Mat-to-Matrix-cong ≡-refl ≡-refl C₁≈C₂ (reduce≥ i (≤-pred (≰⇒> ¬p))) (fromℕ≤ p)
  Mat-to-Matrix-cong {deeper s₁ s₂} {deeper s₁' s₂'} ≡-refl ≡-refl (quad-eq A₁≈A₂ B₁≈B₂ C₁≈C₂ D₁≈D₂) i j | no ¬p | no ¬p' = Mat-to-Matrix-cong ≡-refl ≡-refl D₁≈D₂ (reduce≥ i (≤-pred (≰⇒> ¬p))) (reduce≥ j (≤-pred (≰⇒> ¬p')))


  V+-Homomorphism : {s : Splitting} {n : ℕ} (|s|≡n : splitSize s ≡ n) → (u v : Vec s) →
                    Vec-to-Vector |s|≡n (u v+ v) V≈ Vec-to-Vector |s|≡n (u) V+ Vec-to-Vector |s|≡n (v)
  V+-Homomorphism {one} ≡-refl (Valiant.Concrete.Mat.one x) (Valiant.Concrete.Mat.one x') f0 = R-refl
  V+-Homomorphism {one} ≡-refl (Valiant.Concrete.Mat.one x) (Valiant.Concrete.Mat.one x') (fsuc ())
  V+-Homomorphism {deeper s₁ s₂} ≡-refl (Valiant.Concrete.Mat.two u v) (Valiant.Concrete.Mat.two u' v') i with suc (toℕ i) ≤? splitSize s₁
  V+-Homomorphism {deeper s₁ s₂} ≡-refl (Valiant.Concrete.Mat.two u v) (Valiant.Concrete.Mat.two u' v') i | yes p = V+-Homomorphism ≡-refl u u' (fromℕ≤ p)
  V+-Homomorphism {deeper s₁ s₂} ≡-refl (Valiant.Concrete.Mat.two u v) (Valiant.Concrete.Mat.two u' v') i | no ¬p = V+-Homomorphism ≡-refl v v' (reduce≥ i (≤-pred (≰⇒> ¬p)))

  M+-Homomorphism : {s₁ s₂ : Splitting} {n₁ n₂ : ℕ} (|s₁|≡n₁ : splitSize s₁ ≡ n₁) (|s₂|≡n₂ : splitSize s₂ ≡ n₂) → (A B : Mat s₁ s₂) →
                    Mat-to-Matrix |s₁|≡n₁ |s₂|≡n₂ (A m+ B) M≈ Mat-to-Matrix |s₁|≡n₁ |s₂|≡n₂ A M+ Mat-to-Matrix |s₁|≡n₁ |s₂|≡n₂ B
  M+-Homomorphism {one} {one} ≡-refl ≡-refl (Valiant.Concrete.Mat.Sing x) (Valiant.Concrete.Mat.Sing x') f0 f0 = R-refl
  M+-Homomorphism {one} {one} ≡-refl ≡-refl A B f0 (fsuc ())
  M+-Homomorphism {one} {one} ≡-refl ≡-refl A B (fsuc ()) j
  M+-Homomorphism {deeper s₁ s₂} {one} ≡-refl ≡-refl (Valiant.Concrete.Mat.CVec v) (Valiant.Concrete.Mat.CVec v') i f0 = V+-Homomorphism ≡-refl v v' i
  M+-Homomorphism {deeper s₁ s₂} {one} ≡-refl ≡-refl (Valiant.Concrete.Mat.CVec v) (Valiant.Concrete.Mat.CVec v') i (fsuc ())
  M+-Homomorphism {one} {deeper s₁' s₂} ≡-refl ≡-refl (Valiant.Concrete.Mat.RVec v) (Valiant.Concrete.Mat.RVec v') f0 j = V+-Homomorphism ≡-refl v v' j
  M+-Homomorphism {one} {deeper s₁' s₂} ≡-refl ≡-refl A B (fsuc ()) j
  M+-Homomorphism {deeper s₁ s₂} {deeper s₁' s₂'} ≡-refl ≡-refl (Valiant.Concrete.Mat.quad A B C D) (Valiant.Concrete.Mat.quad A' B' C' D') i j with suc (toℕ i) ≤? splitSize s₁ | suc (toℕ j) ≤? splitSize s₁'
  M+-Homomorphism {deeper s₁ s₂} {deeper s₁' s₂'} ≡-refl ≡-refl (Valiant.Concrete.Mat.quad A B C D) (Valiant.Concrete.Mat.quad A' B' C' D') i j | yes p | yes p' = M+-Homomorphism ≡-refl ≡-refl A A' (fromℕ≤ p) (fromℕ≤ p')
  M+-Homomorphism {deeper s₁ s₂} {deeper s₁' s₂'} ≡-refl ≡-refl (Valiant.Concrete.Mat.quad A B C D) (Valiant.Concrete.Mat.quad A' B' C' D') i j | yes p | no ¬p = M+-Homomorphism ≡-refl ≡-refl B B' (fromℕ≤ p) (reduce≥ j (≤-pred (≰⇒> ¬p)))
  M+-Homomorphism {deeper s₁ s₂} {deeper s₁' s₂'} ≡-refl ≡-refl (Valiant.Concrete.Mat.quad A B C D) (Valiant.Concrete.Mat.quad A' B' C' D') i j | no ¬p | yes p = M+-Homomorphism ≡-refl ≡-refl C C' (reduce≥ i (≤-pred (≰⇒> ¬p))) (fromℕ≤ p)
  M+-Homomorphism {deeper s₁ s₂} {deeper s₁' s₂'} ≡-refl ≡-refl (Valiant.Concrete.Mat.quad A B C D) (Valiant.Concrete.Mat.quad A' B' C' D') i j | no ¬p | no ¬p' = M+-Homomorphism ≡-refl ≡-refl D D' (reduce≥ i (≤-pred (≰⇒> ¬p))) (reduce≥ j (≤-pred (≰⇒> ¬p')))

-- lemmas for reindexing (for example, probably exist in Fin)
  ≤-lemma :  {m n : ℕ} {i : Fin (m + n)} (p : suc (toℕ i) ≤ m) → fromℕ≤ (s≤s p) ≡ fsuc (fromℕ≤ p)
  ≤-lemma (s≤s m≤n) = ≡-refl
  ≤-lemma' : {m n : ℕ} {i : Fin (m + n)} (¬p : suc (toℕ i) ≤ m → ⊥) → reduce≥ (fsuc i) (≰⇒> (λ x → ¬p x)) ≡ reduce≥ i (≤-pred (≰⇒> ¬p))
  ≤-lemma' {zero} ¬p = ≡-refl
  ≤-lemma' {suc n} ¬p = ≡-refl

  two-reindexing : {m n : ℕ} (u : Vector (suc m)) (v : Vector n) → (i : Fin (m + n)) → Two u v (fsuc i) ≈ Two (λ i' →  u (fsuc i')) v i 
  two-reindexing {m} u v i with suc (toℕ i) ≤? m 
  two-reindexing u v i | yes p = reflexive (≡-cong u (≤-lemma p))
  two-reindexing u v i | no ¬p = reflexive (≡-cong v (≤-lemma' ¬p))

  V∙-cong : {m : ℕ} {u u' v v' : Vector m} → u V≈ u' → v V≈ v' → u V∙ v ≈ u' V∙ v'
  V∙-cong {zero} u≈u' v≈v' = R-refl
  V∙-cong {suc n} u≈u' v≈v' = R+-cong (R*-cong (u≈u' f0) (v≈v' f0)) (V∙-cong (λ i → u≈u' (fsuc i)) (λ i → v≈v' (fsuc i)))

  two-V∙ : {m n : ℕ} (u u' : Vector m) (v v' : Vector n) → Two u v V∙ Two u' v' ≈ u V∙ u' R+ v V∙ v'
  two-V∙ {zero} u u' v v' = R-sym (proj₁ R+-identity (v V∙ v')) --begin v V∙ v' ≈⟨ {!!} ⟩ ({!0# R+ v !} ∎)
  two-V∙ {suc n} u u' v v' = begin 
    u f0 R* u' f0 R+ (λ i → Two u v (fsuc i)) V∙ (λ i → Two u' v' (fsuc i)) 
      ≈⟨ R+-cong R-refl (V∙-cong (two-reindexing u v) (two-reindexing u' v')) ⟩
    u f0 R* u' f0 R+ Two (λ i → u (fsuc i)) v V∙ Two (λ i → u' (fsuc i)) v' 
      ≈⟨ R+-cong R-refl (two-V∙ (λ i → u (fsuc i)) (λ i → u' (fsuc i)) v v') ⟩
    u f0 R* u' f0 R+ ((λ i → u (fsuc i)) V∙ (λ i → u' (fsuc i)) R+ v V∙ v')
      ≈⟨ R-sym (R+-assoc (u f0 R* u' f0) ((λ i → u (fsuc i)) V∙ (λ i → u' (fsuc i))) (v V∙ v')) ⟩
    u f0 R* u' f0 R+ (λ i → u (fsuc i)) V∙ (λ i → u' (fsuc i)) R+ v V∙ v' ∎
    where open EqR setoid
  V∙-Homomorphism : {s : Splitting} {n : ℕ} (|s|≡n : splitSize s ≡ n) → (u v : Vec s) → u v∙ v ≈ Vec-to-Vector |s|≡n u V∙ Vec-to-Vector |s|≡n v
  V∙-Homomorphism {one} ≡-refl (Valiant.Concrete.Mat.one x) (Valiant.Concrete.Mat.one x') = trans-∙ R-refl
  V∙-Homomorphism {deeper s₁ s₂} ≡-refl (Valiant.Concrete.Mat.two u v) (Valiant.Concrete.Mat.two u' v') = begin 
    u v∙ u' R+ v v∙ v' 
      ≈⟨ R+-cong (V∙-Homomorphism ≡-refl u u') (V∙-Homomorphism ≡-refl v v') ⟩ 
    Vec-to-Vector ≡-refl u V∙ Vec-to-Vector ≡-refl u' R+
      Vec-to-Vector ≡-refl v V∙ Vec-to-Vector ≡-refl v'
      ≈⟨ R-sym (two-V∙ (Vec-to-Vector ≡-refl u) (Vec-to-Vector ≡-refl u') (Vec-to-Vector ≡-refl v) (Vec-to-Vector ≡-refl v')) ⟩
    Two (Vec-to-Vector ≡-refl u) (Vec-to-Vector ≡-refl v) V∙ Two (Vec-to-Vector ≡-refl u') (Vec-to-Vector ≡-refl v') ∎
    where open EqR setoid

  |⊛-Homomorphism : {s : Splitting} {n : ℕ} (|s|≡n : splitSize s ≡ n) → (v : Vec s) (x : Carrier) → (Vec-to-Vector |s|≡n (v |⊛ x)) V≈ Vec-to-Vector |s|≡n v Vs* x
  |⊛-Homomorphism {one} ≡-refl (Valiant.Concrete.Mat.one x) x' f0 = R-refl
  |⊛-Homomorphism {one} ≡-refl (Valiant.Concrete.Mat.one x) x' (fsuc ())
  |⊛-Homomorphism {deeper s₁ s₂} ≡-refl (Valiant.Concrete.Mat.two u v) x i with suc (toℕ i) ≤? splitSize s₁
  |⊛-Homomorphism {deeper s₁ s₂} ≡-refl (Valiant.Concrete.Mat.two u v) x i | yes p = |⊛-Homomorphism ≡-refl u x (fromℕ≤ p)
  |⊛-Homomorphism {deeper s₁ s₂} ≡-refl (Valiant.Concrete.Mat.two u v) x i | no ¬p = |⊛-Homomorphism ≡-refl v x (reduce≥ i (≤-pred (≰⇒> ¬p)))

  ⊛|-Homomorphism : {s : Splitting} {n : ℕ} (|s|≡n : splitSize s ≡ n) → (x : Carrier) (v : Vec s) → (Vec-to-Vector |s|≡n (x ⊛| v)) V≈ x sV* Vec-to-Vector |s|≡n v
  ⊛|-Homomorphism {one} ≡-refl x (Valiant.Concrete.Mat.one x') f0 = R-refl
  ⊛|-Homomorphism {one} ≡-refl x (Valiant.Concrete.Mat.one x') (fsuc ())
  ⊛|-Homomorphism {deeper s₁ s₂} ≡-refl x (Valiant.Concrete.Mat.two u v) i with suc (toℕ i) ≤? splitSize s₁ 
  ⊛|-Homomorphism {deeper s₁ s₂} ≡-refl x (Valiant.Concrete.Mat.two u v) i | yes p = ⊛|-Homomorphism ≡-refl x u (fromℕ≤ p)
  ⊛|-Homomorphism {deeper s₁ s₂} ≡-refl x (Valiant.Concrete.Mat.two u v) i | no ¬p = ⊛|-Homomorphism ≡-refl x v (reduce≥ i (≤-pred (≰⇒> ¬p)))

  M⊗-Homomorphism :  {s₁ s₂ : Splitting} {n₁ n₂ : ℕ} (|s₁|≡n₁ : splitSize s₁ ≡ n₁) (|s₂|≡n₂ : splitSize s₂ ≡ n₂) → (u : Vec s₁) (v : Vec s₂) → Mat-to-Matrix |s₁|≡n₁ |s₂|≡n₂ (u v⊗ v) M≈ Vec-to-Vector |s₁|≡n₁ u V⊗ Vec-to-Vector |s₂|≡n₂ v
  M⊗-Homomorphism {one} {one} ≡-refl ≡-refl (Valiant.Concrete.Mat.one x) (Valiant.Concrete.Mat.one x') f0 f0 = R-refl
  M⊗-Homomorphism {one} {one} ≡-refl ≡-refl (Valiant.Concrete.Mat.one x) (Valiant.Concrete.Mat.one x') f0 (fsuc ())
  M⊗-Homomorphism {one} {one} ≡-refl ≡-refl (Valiant.Concrete.Mat.one x) (Valiant.Concrete.Mat.one x') (fsuc ()) j
  M⊗-Homomorphism {deeper s₁ s₂} {one} ≡-refl ≡-refl (Valiant.Concrete.Mat.two u v) (Valiant.Concrete.Mat.one x) i f0 with suc (toℕ i) ≤? splitSize s₁
  M⊗-Homomorphism {deeper s₁ s₂} {one} ≡-refl ≡-refl (Valiant.Concrete.Mat.two u v) (Valiant.Concrete.Mat.one x) i f0 | yes p = |⊛-Homomorphism ≡-refl u x (fromℕ≤ p)
  M⊗-Homomorphism {deeper s₁ s₂} {one} ≡-refl ≡-refl (Valiant.Concrete.Mat.two u v) (Valiant.Concrete.Mat.one x) i f0 | no ¬p = |⊛-Homomorphism ≡-refl v x (reduce≥ i (≤-pred (≰⇒> ¬p)))
  M⊗-Homomorphism {deeper s₁ s₂} {one} ≡-refl ≡-refl (Valiant.Concrete.Mat.two u v) (Valiant.Concrete.Mat.one x) i (fsuc ())
  M⊗-Homomorphism {one} {deeper s₁' s₂} ≡-refl ≡-refl (Valiant.Concrete.Mat.one x) (Valiant.Concrete.Mat.two u v) f0 j = ⊛|-Homomorphism ≡-refl x (Valiant.Concrete.Mat.two u v) j
  M⊗-Homomorphism {one} {deeper s₁' s₂} ≡-refl ≡-refl (Valiant.Concrete.Mat.one x) (Valiant.Concrete.Mat.two u v) (fsuc ()) j
  M⊗-Homomorphism {deeper s₁ s₂} {deeper s₁' s₂'} ≡-refl ≡-refl (Valiant.Concrete.Mat.two u v) (Valiant.Concrete.Mat.two u' v') i j with suc (toℕ i) ≤? splitSize s₁ | suc (toℕ j) ≤? splitSize s₁' 
  M⊗-Homomorphism {deeper s₁ s₂} {deeper s₁' s₂'} ≡-refl ≡-refl (Valiant.Concrete.Mat.two u v) (Valiant.Concrete.Mat.two u' v') i j | yes p | yes p' = M⊗-Homomorphism ≡-refl ≡-refl u u' (fromℕ≤ p) (fromℕ≤ p')
  M⊗-Homomorphism {deeper s₁ s₂} {deeper s₁' s₂'} ≡-refl ≡-refl (Valiant.Concrete.Mat.two u v) (Valiant.Concrete.Mat.two u' v') i j | yes p | no ¬p = M⊗-Homomorphism ≡-refl ≡-refl u v' (fromℕ≤ p) (reduce≥ j (≤-pred (≰⇒> ¬p)))
  M⊗-Homomorphism {deeper s₁ s₂} {deeper s₁' s₂'} ≡-refl ≡-refl (Valiant.Concrete.Mat.two u v) (Valiant.Concrete.Mat.two u' v') i j | no ¬p | yes p = M⊗-Homomorphism ≡-refl ≡-refl v u' (reduce≥ i (≤-pred (≰⇒> ¬p))) (fromℕ≤ p)
  M⊗-Homomorphism {deeper s₁ s₂} {deeper s₁' s₂'} ≡-refl ≡-refl (Valiant.Concrete.Mat.two u v) (Valiant.Concrete.Mat.two u' v') i j | no ¬p | no ¬p' = M⊗-Homomorphism ≡-refl ≡-refl v v' (reduce≥ i (≤-pred (≰⇒> ¬p))) (reduce≥ j (≤-pred (≰⇒> ¬p')))


-- multiplying a row of a four with a col of another four is equal to 
--row-col-mul₁ : {m n : ℕ} {A A' : Matrix m m} {B B' : Matrix m n} {C C' : Matrix n m} {D D' : Matrix n n} (i : Fin (m + n)) (j : Fin (m + n)) (i<m : suc (toℕ i) ≤ m) (j<m : suc (toℕ j) ≤ m ) →  row i (Four A B C D) V∙ col j (Four A' B' C' D') ≈ row (fromℕ≤ i<m) A V∙ col (fromℕ≤ j<m) A' R+ row (fromℕ≤ i<m) B V∙ col (fromℕ≤ j<m) C'
--row-col-mul₁ {zero} {zero} () j i<m j<m
--row-col-mul₁ {zero} {suc n} i j i<m j<m = {!!}
--row-col-mul₁ {suc n} {suc n'} i j i<m j<m = {!!}
--row-col-mul₁ {suc n} {zero} f0 f0 (s≤s m≤n) (s≤s m≤n') = {!!}
--row-col-mul₁ {suc n} {zero} f0 (fsuc i) i<m j<m = {!!}
--row-col-mul₁ {suc n} {zero} (fsuc i) j i<m j<m = {!!}

  proofs-equal : {m n : ℕ} → (p p' : m ≤ n) → p ≡ p'
  proofs-equal z≤n z≤n = ≡-refl
  proofs-equal (s≤s m≤n) (s≤s m≤n') = ≡-cong s≤s (proofs-equal m≤n m≤n')




-- this might not have been proved before, as Matrix m n is not a ring.
  M+-cong : {m n : ℕ} {A A' B B' : Matrix m n} → A M≈ A' → B M≈ B' → A M+ B M≈ A' M+ B'
  M+-cong A≈A' B≈B' i j = R+-cong (A≈A' i j) (B≈B' i j)

  row-lemma : {a b c d : ℕ} {A : Matrix a b} {B : Matrix a d} (C : Matrix c b) (D : Matrix c d) (i : Fin (a + c)) (i<m : suc (toℕ i) ≤ a) → row i (Four A B C D) V≈ Two (row (fromℕ≤ i<m) A) (row (fromℕ≤ i<m) B)
  row-lemma {a} {b} C D i i<m j with suc (toℕ i) ≤? a | suc (toℕ j) ≤? b
  row-lemma {A = A} C D i i<m j | yes p | yes p' = reflexive (≡-cong (λ x → A (fromℕ≤ x) (fromℕ≤ p')) (proofs-equal p i<m))
  row-lemma {B = B} C D i i<m j | yes p | no ¬p = reflexive (≡-cong (λ x → B (fromℕ≤ x) (reduce≥ j (≤-pred (≰⇒> ¬p)))) (proofs-equal p i<m))
  row-lemma C D i i<m j | no ¬p | _ = ⊥-elim (¬p i<m)

  col-lemma : {a b c d : ℕ} {A : Matrix a b} (B : Matrix a d) {C : Matrix c b} (D : Matrix c d) (j : Fin (b + d)) (j<m : suc (toℕ j) ≤ b) → col j (Four A B C D) V≈ Two (col (fromℕ≤ j<m) A) (col (fromℕ≤ j<m) C)
  col-lemma {a} {b} B D j j<m k with suc (toℕ k) ≤? a | suc (toℕ j) ≤? b 
  col-lemma {A = A} B D j j<m k | yes p | yes p' = reflexive (≡-cong (λ x → A (fromℕ≤ p) (fromℕ≤ x)) (proofs-equal p' j<m))
  col-lemma B {C = C} D j j<m k | no ¬p | yes p = reflexive (≡-cong (λ x → C (reduce≥ k (≤-pred (≰⇒> ¬p))) (fromℕ≤ x)) (proofs-equal p j<m))
  col-lemma B D j j<m k | _ | no ¬p = ⊥-elim (¬p j<m)

  row-col-mul₁ : {m n : ℕ} (A A' : Matrix m m) (B B' : Matrix m n) (C C' : Matrix n m) (D D' : Matrix n n) (i : Fin (m + n)) (j : Fin (m + n)) (i<m : suc (toℕ i) ≤ m) (j<m : suc (toℕ j) ≤ m ) →  row i (Four A B C D) V∙ col j (Four A' B' C' D') ≈ row (fromℕ≤ i<m) A V∙ col (fromℕ≤ j<m) A' R+ row (fromℕ≤ i<m) B V∙ col (fromℕ≤ j<m) C'
  row-col-mul₁ {m} {n} A A' B B' C C' D D' i j i<m j<m = begin 
    row i (Four A B C D) V∙ col j (Four A' B' C' D') 
      ≈⟨ V∙-cong (row-lemma C D i i<m) (col-lemma B' D' j j<m) ⟩ -- V∙-cong
    Two (row (fromℕ≤ i<m) A) (row (fromℕ≤ i<m) B) V∙ Two (col (fromℕ≤ j<m) A') (col (fromℕ≤ j<m) C')
      ≈⟨ two-V∙ (row (fromℕ≤ i<m) A) (col (fromℕ≤ j<m) A') (row (fromℕ≤ i<m) B) (col (fromℕ≤ j<m) C') ⟩ -- two-V∙
    row (fromℕ≤ i<m) A V∙ col (fromℕ≤ j<m) A' R+ row (fromℕ≤ i<m) B V∙ col (fromℕ≤ j<m) C' ∎
    where open EqR setoid

  row-col-mul : {a b c d e f : ℕ} (A : Matrix a b) (B : Matrix a c) (C : Matrix d b) (D : Matrix d c ) (A' : Matrix b e) (B' : Matrix b f) (C' : Matrix c e) (D' : Matrix c f) (i : Fin (a + d)) (j : Fin (e + f)) (i<m : suc (toℕ i) ≤ a) (j<m : suc (toℕ j) ≤ e) →  row i (Four A B C D) V∙ col j (Four A' B' C' D') ≈ row (fromℕ≤ i<m) A V∙ col (fromℕ≤ j<m) A' R+ row (fromℕ≤ i<m) B V∙ col (fromℕ≤ j<m) C'
  row-col-mul {m} {n} A B C D A' B' C' D' i j i<m j<m = begin 
    row i (Four A B C D) V∙ col j (Four A' B' C' D') 
      ≈⟨ V∙-cong (row-lemma C D i i<m) (col-lemma B' D' j j<m) ⟩ -- V∙-cong
    Two (row (fromℕ≤ i<m) A) (row (fromℕ≤ i<m) B) V∙ Two (col (fromℕ≤ j<m) A') (col (fromℕ≤ j<m) C')
      ≈⟨ two-V∙ (row (fromℕ≤ i<m) A) (col (fromℕ≤ j<m) A') (row (fromℕ≤ i<m) B) (col (fromℕ≤ j<m) C') ⟩ -- two-V∙
    row (fromℕ≤ i<m) A V∙ col (fromℕ≤ j<m) A' R+ row (fromℕ≤ i<m) B V∙ col (fromℕ≤ j<m) C' ∎
    where open EqR setoid

  row-col-mul' : {a b c d e f : ℕ} (A : Matrix a b) (B : Matrix a c) (C : Matrix d b) (D : Matrix d c ) (A' : Matrix b e) (B' : Matrix b f) (C' : Matrix c e) (D' : Matrix c f) (i : Fin (a + d)) (j : Fin (e + f)) (i<m : suc (toℕ i) ≤ a) (j<m : suc (toℕ j) ≤ e) →  row i (Four A B C D) V∙ col j (Four A' B' C' D') ≈ row (fromℕ≤ i<m) A V∙ col (fromℕ≤ j<m) A' R+ row (fromℕ≤ i<m) B V∙ col (fromℕ≤ j<m) C'
  row-col-mul' {m} {n} A B C D A' B' C' D' i j i<m j<m = begin 
    row i (Four A B C D) V∙ col j (Four A' B' C' D') 
      ≈⟨ V∙-cong (row-lemma C D i i<m) (col-lemma B' D' j j<m) ⟩ -- V∙-cong
    Two (row (fromℕ≤ i<m) A) (row (fromℕ≤ i<m) B) V∙ Two (col (fromℕ≤ j<m) A') (col (fromℕ≤ j<m) C')
      ≈⟨ two-V∙ (row (fromℕ≤ i<m) A) (col (fromℕ≤ j<m) A') (row (fromℕ≤ i<m) B) (col (fromℕ≤ j<m) C') ⟩ -- two-V∙
    row (fromℕ≤ i<m) A V∙ col (fromℕ≤ j<m) A' R+ row (fromℕ≤ i<m) B V∙ col (fromℕ≤ j<m) C' ∎
    where open EqR setoid


{-row-col : {m n o p q r : ℕ} (A : Matrix m n) (B : Matrix m o) (C : Matrix p n) (D : Matrix p o) (A' : Matrix n q) (B' : Matrix n r) (C' : Matrix o q) (D' : Matrix o r) → (i : Fin (m + p)) → (j : Fin (q + r)) → Four (A M* A' M+ B M* C') (A M* B' M+ B M* D') (C M* A' M+ D M* C')
                  (C M* B' M+ D M* D')
                  i j
                  ≈
          row i (Four A B C D) V∙ col j (Four A' B' C' D')
row-col {m = m} {q = q} A B C D A' B' C' D' i j with suc (toℕ i) ≤? m | suc (toℕ j) ≤? q 
...| aa | bb = {!!}
  where open EqR setoid

row-col' : {m n o p q r : ℕ} (A : Matrix m n) (B : Matrix m o) (C : Matrix p n) (D : Matrix p o) (A' : Matrix n q) (B' : Matrix n r) (C' : Matrix o q) (D' : Matrix o r) → (i : Fin (m + p)) → (j : Fin (q + r)) → Four (A M* A' M+ B M* C') (A M* B' M+ B M* D') (C M* A' M+ D M* C')
                  (C M* B' M+ D M* D')
                  i j
                  ≈
          row i (Four A B C D) V∙ col j (Four A' B' C' D')
row-col' {m} {zero} {o} {p} {q} {r} A B C D A' B' C' D' i j = {!!} --with suc (toℕ i) ≤? m | suc (toℕ j) ≤? q
--row-col' {m} {zero} {o} {p} {q} {r} A B C D A' B' C' D' i j | afs | vavs = {!!}
row-col' {m} {suc n} {o} {p} {q} {r} A B C D A' B' C' D' i j with suc (toℕ i) ≤? m | suc (toℕ j) ≤? q
row-col' {m} {suc n} A B C D A' B' C' D' i j | yes p' | yes p0 = begin 
  A (fromℕ≤ p') f0 R* A' f0 (fromℕ≤ p0)   R+   (λ i' → A (fromℕ≤ p') (fsuc i')) V∙ (λ i' → A' (fsuc i') (fromℕ≤ p0))        R+         B (fromℕ≤ p') V∙ (λ k → C' k (fromℕ≤ p0))   
    ≈⟨ R+-assoc (A (fromℕ≤ p') f0 R* A' f0 (fromℕ≤ p0)) ((λ i' → A (fromℕ≤ p') (fsuc i')) V∙
                                                           (λ i' → A' (fsuc i') (fromℕ≤ p0))) (B (fromℕ≤ p') V∙ (λ k → C' k (fromℕ≤ p0))) ⟩ 
  A (fromℕ≤ p') f0 R* A' f0 (fromℕ≤ p0) R+
    ((λ i' → A (fromℕ≤ p') (fsuc i')) V∙
    (λ i' → A' (fsuc i') (fromℕ≤ p0))
    R+ B (fromℕ≤ p') V∙ (λ k → C' k (fromℕ≤ p0)))
    ≈⟨ R+-cong R-refl subpf ⟩
  A (fromℕ≤ p') f0 R* A' f0 (fromℕ≤ p0) R+ _ ∎
  where open EqR setoid
        subpf = begin 
          (λ i' → A (fromℕ≤ p') (fsuc i')) V∙
            (λ i' → A' (fsuc i') (fromℕ≤ p0))
            R+ B (fromℕ≤ p') V∙ (λ k → C' k (fromℕ≤ p0)) 
            ≈⟨ {!!} ⟩ 
          _
            ≈⟨ {!row-col' {m} {n} ? ? ? ? ? ? ? ? ? ?!} ⟩
          {!(λ i' →
               Valiant.Abstract.Matrix.Four NAR A B C D i (fsuc i') | yes p'
               | (suc (suc (toℕ i')) ≤? suc n | suc (toℕ i') ≤? n))
            V∙
            (λ i' →
               Valiant.Abstract.Matrix.Four NAR A' B' C' D' (fsuc i') j
               | (suc (suc (toℕ i')) ≤? suc n | suc (toℕ i') ≤? n) | yes p0)!} ∎
row-col' {m} {suc n} A B C D A' B' C' D' i j | yes p' | no ¬p = {!!}
row-col' {m} {suc n} A B C D A' B' C' D' i j | no ¬p | bb = {!!}
--Goal: (λ i' → A (fromℕ≤ p') (fsuc i')) V∙
--      (λ i' → A' (fsuc i') (fromℕ≤ p0))
--      R+ B (fromℕ≤ p') V∙ (λ k → C' k (fromℕ≤ p0))
--      ≈
--      (λ i' →
--         Valiant.Abstract.Matrix.Four NAR A B C D i (fsuc i') | yes p'
--         | (suc (suc (toℕ i')) ≤? suc n | suc (toℕ i') ≤? n))
--      V∙
--      (λ i' →
--         Valiant.Abstract.Matrix.Four NAR A' B' C' D' (fsuc i') j
--         | (suc (suc (toℕ i')) ≤? suc n | suc (toℕ i') ≤? n) | yes p0)
--  where open EqR setoid
-}
  Four-cong : {m n o p : ℕ} {a a' : Matrix m n} {b b' : Matrix m o} {c c' : Matrix p n} {d d' : Matrix p o} → a M≈ a' → b M≈ b' → c M≈ c' → d M≈ d' → Four a b c d M≈ Four a' b' c' d'
  Four-cong {m} {n} a≈a' b≈b' c≈c' d≈d' i j with suc (toℕ i) ≤? m | suc (toℕ j) ≤? n
  Four-cong a≈a' b≈b' c≈c' d≈d' i j | yes p | yes p' = a≈a' (fromℕ≤ p) (fromℕ≤ p')
  Four-cong a≈a' b≈b' c≈c' d≈d' i j | yes p' | no ¬p = b≈b' (fromℕ≤ p') (reduce≥ j (≤-pred (≰⇒> ¬p)))
  Four-cong a≈a' b≈b' c≈c' d≈d' i j | no ¬p | yes p' = c≈c' (reduce≥ i (≤-pred (≰⇒> ¬p))) (fromℕ≤ p')
  Four-cong a≈a' b≈b' c≈c' d≈d' i j | no ¬p | no ¬p' = d≈d' (reduce≥ i (≤-pred (≰⇒> ¬p))) (reduce≥ j (≤-pred (≰⇒> ¬p')))

  first-row-four : {m n o p : ℕ} (A : Matrix (suc m) n) (B : Matrix (suc m) o) (C : Matrix p n) (D : Matrix p o) → Two (row f0 A) (row f0 B) V≈ row f0 (Four A B C D)
  first-row-four {m} {n} A B C D i with suc (toℕ i) ≤? n
  first-row-four A B C D i | yes p = R-refl
  first-row-four A B C D i | no ¬p = R-refl

  first-col-four : {m n o p : ℕ} (A : Matrix m (suc n)) (B : Matrix m o) (C : Matrix p (suc n)) (D : Matrix p o) → Two (col f0 A) (col f0 C) V≈ col f0 (Four A B C D)
  first-col-four {m} A B C D i with suc (toℕ i) ≤? m 
  first-col-four A B C D i | yes p' = R-refl
  first-col-four A B C D i | no ¬p = R-refl --{!Two (col f0 B) (col f0 D)!} Fin (.m + suc .p) → Carrier
  
  four-empty-row : {n o p : ℕ} (A : Matrix zero n) (B : Matrix zero o) (C : Matrix p n) (D : Matrix p o) → (i : Fin p) → row i (Four A B C D) V≈ Two (row i C) (row i D)
  four-empty-row {n} A B C D i j with suc (toℕ i) ≤? zero | suc (toℕ j) ≤? n
  four-empty-row A B C D i j | yes () | _
  four-empty-row A B C D i j | no ¬p | yes p' = R-refl
  four-empty-row A B C D i j | no ¬p | no ¬p' = R-refl
  
  four-empty-col : {m o p : ℕ} (A : Matrix m zero) (B : Matrix m o) (C : Matrix p zero) (D : Matrix p o) → (j : Fin o) → col j (Four A B C D) V≈ Two (col j B) (col j D)
  four-empty-col {m} A B C D j k with suc (toℕ k) ≤? m | suc (toℕ j) ≤? zero 
  four-empty-col A B C D j k | _ | yes ()
  four-empty-col A B C D j k | yes p' | no ¬p = R-refl
  four-empty-col A B C D j k | no ¬p | no ¬p' = R-refl


  Four-index-change : {m n o p : ℕ} (A : Matrix (suc m) n) (B : Matrix (suc m) o) (C : Matrix p n) (D : Matrix p o) → (i : Fin (m + p)) → (j : Fin (n + o)) → Four A B C D (fsuc i) j ≈ Four (λ i' j' → A (fsuc i') j') (λ i' j' → B (fsuc i') j' ) C D i j
  Four-index-change {m} {n} A B C D i j with suc (toℕ i) ≤? m | suc (toℕ j) ≤? n 
  Four-index-change A0 B0 C0 D0 i' j' | yes p0 | yes p1 = reflexive (≡-cong₂ A0 (≤-lemma p0) ≡-refl)
  Four-index-change A0 B0 C0 D0 i' j' | yes p0 | no ¬p = reflexive (≡-cong₂ B0 (≤-lemma p0) ≡-refl)
  Four-index-change A0 B0 C0 D0 i' j' | no ¬p' | yes p' = reflexive (≡-cong₂ C0 (≤-lemma' ¬p') ≡-refl)
  Four-index-change A0 B0 C0 D0 i' j' | no ¬p' | no ¬p0 = reflexive (≡-cong₂ D0 (≤-lemma' ¬p') ≡-refl)

  Four-index-change-col : {m n o p : ℕ} (A : Matrix m (suc n)) (B : Matrix m o) (C : Matrix p (suc n)) (D : Matrix p o) → (i : Fin (m + p)) → (j : Fin (n + o)) → Four A B C D i (fsuc j) ≈ Four (λ i' j' → A i' (fsuc j')) B (λ i' j' → C i' (fsuc j')) D i j
  Four-index-change-col {m} {n} A B C D i j with suc (toℕ i) ≤? m | suc (toℕ j) ≤? n
  Four-index-change-col A B C D i j | yes p' | yes p0 = reflexive (≡-cong₂ A ≡-refl (≤-lemma p0))
  Four-index-change-col A B C D i j | yes p' | no ¬p = reflexive (≡-cong₂ B ≡-refl (≤-lemma' ¬p))
  Four-index-change-col A B C D i j | no ¬p | yes p' = reflexive (≡-cong₂ C ≡-refl (≤-lemma p'))
  Four-index-change-col A B C D i j | no ¬p | no ¬p' = reflexive (≡-cong₂ D ≡-refl (≤-lemma' ¬p'))


  row-col'' : {m n o p q r : ℕ} (A : Matrix m n) (B : Matrix m o) (C : Matrix p n) (D : Matrix p o) (A' : Matrix n q) (B' : Matrix n r) (C' : Matrix o q) (D' : Matrix o r) → (i : Fin (m + p)) → (j : Fin (q + r)) → Four (A M* A' M+ B M* C') (A M* B' M+ B M* D') (C M* A' M+ D M* C') (C M* B' M+ D M* D')
                  i j
                    ≈
            row i (Four A B C D) V∙ col j (Four A' B' C' D')
  row-col'' {zero} {n} {o} {p} {zero} A B C D A' B' C' D' i j = begin 
    C i V∙ (λ k → B' k j) R+ D i V∙ (λ k → D' k j)
      ≈⟨ R-sym (two-V∙ (row i C) (col j B') (row i D) (col j D')) ⟩
    Two (row i C) (row i D) V∙ Two (col j B') (col j D')
      ≈⟨ R-sym (V∙-cong (four-empty-row A B C D i) (four-empty-col A' B' C' D' j)) ⟩
    row i (Four A B C D) V∙ col j (Four A' B' C' D') ∎
    where open EqR setoid
  row-col'' {zero} {n} {o} {p} {suc n'} A B C D A' B' C' D' i f0 = begin 
    C i V∙ (λ k → A' k f0) R+ D i V∙ (λ k → C' k f0) 
      ≈⟨ R-sym (two-V∙ (row i C) (col f0 A') (row i D) (col f0 C')) ⟩
    Two (row i C) (row i D) V∙ Two (col f0 A') (col f0 C')
    ≈⟨ R-sym (V∙-cong (four-empty-row A B C D i) (λ i' → R-sym (first-col-four A' B' C' D' i'))) ⟩ 
    row i (Four A B C D) V∙ col f0 (Four A' B' C' D') ∎
    where open EqR setoid
--row-col'' {zero} {n} {o} {p} {suc n'} A B C D A' B' C' D' i (fsuc i') = {!!}
--row-col'' {zero} A B C D A' B' C' D' (fsuc i) j = {!!}
--row-col'' {suc n} {n'} {o} {p} {zero} A B C D A' B' C' D' f0 f0 = {!!}
--row-col'' {suc n} {n'} {o} {p} {zero} A B C D A' B' C' D' f0 (fsuc i) = {!!}
--row-col'' {suc n} {n'} {o} {p} {suc n0} A B C D A' B' C' D' f0 f0 = {!!}
--row-col'' {suc n} {n'} {o} {p} {suc n0} A B C D A' B' C' D' f0 (fsuc i) = {!!}
  row-col'' {suc n} {n'} {o} {p} {zero} A B C D A' B' C' D' f0 j = begin 
    (row f0 A) V∙ (col j B') R+ (row f0 B) V∙ (col j D') 
      ≈⟨ R-sym (two-V∙ (row f0 A) (col j B') (row f0 B) (col j D')) ⟩ 
    Two (row f0 A) (row f0 B) V∙ Two (col j B') (col j D')
      ≈⟨ V∙-cong (first-row-four A B C D) (λ i' → R-sym (four-empty-col A' B' C' D' j i')) ⟩ 
    row f0 (Four A B C D) V∙ col j (Four A' B' C' D') ∎
    where open EqR setoid
        --first-col-four' : {m n p : ℕ} (A : Matrix m zero) (B : Matrix m (suc n)) (C : Matrix p zero) (D : Matrix p (suc n)) → Two (col f0 B) (col f0 D) V≈ col f0 (Four A B C D)
        --first-col-four' A B C D = {!col f0 (Four A B C D)!} 
--row-col'' {suc n} {n'} {o} {p} {zero} A B C D A' B' C' D' f0 (fsuc i) = {!!} -- with row-col'' {n} {n'} {o} {p} {zero} A B C D A' ? C' ? f0 (i) 
--...| aa = {!!}
{-Goal: A f0 V∙ (λ k → B' k (fsuc i)) R+
      B f0 V∙ (λ k → D' k (fsuc i))
      ≈
      (λ k →
         Valiant.Abstract.Matrix.Four NAR A B C D f0 k | yes (s≤s z≤n)
         | suc (toℕ k) ≤? n')
      V∙
      (λ k →
         Valiant.Abstract.Matrix.Four NAR A' B' C' D' k (fsuc i)
         | suc (toℕ k) ≤? n' | no .Data.Nat.absurd)
-}
--row-col'' {suc n} {n'} {o} {p} {suc n0} A B C D A' B' C' D' f0 j with toℕ j ≤? n0
  row-col'' {suc n} {n'} {o} {p} {suc n0} A B C D A' B' C' D' f0 f0 = begin 
    A f0 V∙ (λ k → A' k f0) R+ B f0 V∙ (λ k → C' k f0) 
      ≈⟨ R-sym (two-V∙ (row f0 A) (col f0 A') (row f0 B) (col f0 C')) ⟩
    Two (row f0 A) (row f0 B) V∙ Two (col f0 A') (col f0 C')
      ≈⟨ V∙-cong (first-row-four A B C D) (first-col-four A' B' C' D') ⟩
    row f0 (Four A B C D) V∙ col f0 (Four A' B' C' D') ∎
    where open EqR setoid
  row-col'' {m} {n'} {o} {p} {suc n0} A B C D A' B' C' D' i (fsuc j) = begin
    Four 
      (λ i' j' → A i' V∙ (λ k → A' k j') R+ B i' V∙ (λ k → C' k j'))
      (λ i' j' → A i' V∙ (λ k → B' k j') R+ B i' V∙ (λ k → D' k j'))
      (λ i' j' → C i' V∙ (λ k → A' k j') R+ D i' V∙ (λ k → C' k j'))
      (λ i' j' → C i' V∙ (λ k → B' k j') R+ D i' V∙ (λ k → D' k j')) i
      (fsuc j)
      ≈⟨  Four-index-change-col (λ i' j' → A i' V∙ (λ k → A' k j') R+ B i' V∙ (λ k → C' k j')) (λ i' j' → A i' V∙ (λ k → B' k j') R+ B i' V∙ (λ k → D' k j')) (λ i' j' → C i' V∙ (λ k → A' k j') R+ D i' V∙ (λ k → C' k j')) (λ i' j' → C i' V∙ (λ k → B' k j') R+ D i' V∙ (λ k → D' k j')) i j ⟩
    Valiant.Abstract.Matrix.Four NAR
      (A M* (λ i' j' → A' i' (fsuc j')) M+
      B M* (λ i' j' → C' i' (fsuc j')))
      (A M* B' M+ B M* D')
      (C M* (λ i' j' → A' i' (fsuc j')) M+
      D M* (λ i' j' → C' i' (fsuc j')))
      (C M* B' M+ D M* D') i j
      ≈⟨ row-col'' {m} {n'} {o} {p} {n0} A B C D (λ i' j' → A' i' (fsuc j')) B' (λ i' j' → C' i' (fsuc j')) D' i j ⟩
    row i (Four A B C D) V∙
      (λ i' →
        Four (λ i0 j' → A' i0 (fsuc j')) B' (λ i0 j' → C' i0 (fsuc j')) D'
        i' j)
      ≈⟨ V∙-cong (λ i' → R-refl)
                 (λ i' → R-sym (Four-index-change-col A' B' C' D' i' j)) ⟩
    (λ i' → row i (Four A B C D) i') V∙
      (λ i' → Four A' B' C' D' i' (fsuc j)) ∎
    where open EqR setoid
--row-col'' {suc n} {n'} {o} {p} {suc n0} A B C D A' B' C' D' f0 j | no ¬p = {!!} --begin 
{-  Goal: (Valiant.Abstract.Matrix.Four NAR
       (λ i' j' → A i' V∙ (λ k → A' k j') R+ B i' V∙ (λ k → C' k j'))
       (λ i' j' → A i' V∙ (λ k → B' k j') R+ B i' V∙ (λ k → D' k j'))
       (λ i' j' → C i' V∙ (λ k → A' k j') R+ D i' V∙ (λ k → C' k j'))
       (λ i' j' → C i' V∙ (λ k → B' k j') R+ D i' V∙ (λ k → D' k j')) i
       (fsuc j)
       | suc (toℕ i) ≤? m
       | (suc (suc (toℕ j)) ≤? suc n0 | suc (toℕ j) ≤? n0))
      ≈
      (Valiant.Abstract.Matrix.Four NAR
       (λ i' j' →
          A i' V∙ (λ k → A' k (fsuc j')) R+ B i' V∙ (λ k → C' k (fsuc j')))
       (λ i' j' → A i' V∙ (λ k → B' k j') R+ B i' V∙ (λ k → D' k j'))
       (λ i' j' →
          C i' V∙ (λ k → A' k (fsuc j')) R+ D i' V∙ (λ k → C' k (fsuc j')))
       (λ i' j' → C i' V∙ (λ k → B' k j') R+ D i' V∙ (λ k → D' k j')) i j
       | suc (toℕ i) ≤? m | suc (toℕ j) ≤? n0)

-}
  
--with suc (toℕ j) ≤? q
--row-col'' {suc n} A B C D A' B' C' D' f0 j | yes p = {!!}
--row-col'' {suc n} A B C D A' B' C' D' f0 j | no ¬p = {!!}
  row-col'' {suc n} A B C D A' B' C' D' (fsuc i) j with row-col'' {n} (λ i' j' → A (fsuc i') j') (λ i' j' → B (fsuc i') j') C D A' B' C' D' i j --(λ i' j' → A (fsuc i') V∙ (λ k → A' k j')) (λ i' j' → B (fsuc i') V∙ (λ k → C' k j')) (λ i' j' → C i' V∙ (λ k → A' k j')) {!!} {!!} {!!} {!!} {!!}  i j
  ...| aa  = begin 
    Valiant.Abstract.Matrix.Four NAR
      (λ i' j' → A i' V∙ (λ k → A' k j') R+ B i' V∙ (λ k → C' k j'))
      (λ i' j' → A i' V∙ (λ k → B' k j') R+ B i' V∙ (λ k → D' k j'))
      (λ i' j' → C i' V∙ (λ k → A' k j') R+ D i' V∙ (λ k → C' k j'))
      (λ i' j' → C i' V∙ (λ k → B' k j') R+ D i' V∙ (λ k → D' k j'))
      (fsuc i) j 
      ≈⟨ Four-index-change (λ i' j' → A i' V∙ (λ k → A' k j') R+ B i' V∙ (λ k → C' k j')) (λ i' j' → A i' V∙ (λ k → B' k j') R+ B i' V∙ (λ k → D' k j')) (λ i' j' → C i' V∙ (λ k → A' k j') R+ D i' V∙ (λ k → C' k j')) (λ i' j' → C i' V∙ (λ k → B' k j') R+ D i' V∙ (λ k → D' k j')) i j ⟩ --index-change {!Four A B C D!} {!!} {!!} ⟩
    Valiant.Abstract.Matrix.Four NAR
      (λ i' j' →
        A (fsuc i') V∙ (λ k → A' k j') R+ B (fsuc i') V∙ (λ k → C' k j'))
      (λ i' j' →
        A (fsuc i') V∙ (λ k → B' k j') R+ B (fsuc i') V∙ (λ k → D' k j'))
      (λ i' j' → C i' V∙ (λ k → A' k j') R+ D i' V∙ (λ k → C' k j'))
      (λ i' j' → C i' V∙ (λ k → B' k j') R+ D i' V∙ (λ k → D' k j')) i j
      ≈⟨ aa ⟩
    (λ i' → Four (λ i0 → A (fsuc i0)) (λ i0 → B (fsuc i0)) C D i i') V∙
      (λ k → Valiant.Abstract.Matrix.Four NAR A' B' C' D' k j)
      ≈⟨ V∙-cong (λ i' → R-sym (Four-index-change A B C D i i')) (λ i' → R-refl) ⟩
    (λ i' → Four A B C D (fsuc i) i') V∙
      (λ i' → Valiant.Abstract.Matrix.Four NAR A' B' C' D' i' j) ∎ --with suc (toℕ i) ≤? m | suc (toℕ j) ≤? q
    where open EqR setoid

        --V∙-Four-index-change : {m n o p : ℕ} (A : Matrix (suc m) n) (B : Matrix (suc m) o) (C : Matrix p n) (D : Matrix p o) → (i : Fin (m + p)) → (j : Fin (n + o)) → Four (λ i' j' → A (fsuc i') j') (λ i' j' → B (fsuc i') j' ) C D i j
  --      V∙-Four-index-change = {!!}

-- funktion som returnerar Four med "with"
--Four : ∀ {m n o p} → Matrix m n → Matrix m o → 
--                      Matrix p n → Matrix p o → 

  Two-cong : {m n : ℕ} {u u' : Vector m} {v v' : Vector n} → u V≈ u' → v V≈ v' → Two u v V≈ Two u' v'
--Two-cong {zero} u≈u' v≈v' i = {!!}
  Two-cong {n} u≈u' v≈v' i with suc (toℕ i) ≤? n
  Two-cong u≈u' v≈v' i | yes p = u≈u' (fromℕ≤ p)
  Two-cong u≈u' v≈v' i | no ¬p = v≈v' (reduce≥ i (≤-pred (≰⇒> ¬p)))

  V+-cong : {m : ℕ} {u u' v v' : Vector m} → u V≈ u' → v V≈ v' → u V+ v V≈ u' V+ v'
  V+-cong u≈u' v≈v' i = R+-cong (u≈u' i) (v≈v' i)

  row-Four-Two : {m n o p : ℕ} → (A : Matrix m n) → (B : Matrix m o) → (C : Matrix p n) → (D : Matrix p o) → (u : Vector n) (v : Vector o) → (i : Fin (m + p)) → Two (A MV* u V+ B MV* v) (C MV* u V+ D MV* v) i ≈ row i (Four A B C D) V∙ Two u v
  row-Four-Two {zero} A B C D u v i = begin 
    row i C V∙ u R+ row i D V∙ v 
      ≈⟨ R-sym (two-V∙ (row i C) u (row i D) v) ⟩ 
    Two (row i C) (row i D) V∙ Two u v
      ≈⟨ V∙-cong (λ i' → R-sym (four-empty-row A B C D i i')) (λ i' → R-refl) ⟩ 
    row i (Four A B C D) V∙ Two u v ∎
    where open EqR setoid
  row-Four-Two {suc n} A B C D u v f0 = begin 
    row f0 A V∙ u R+ row f0 B V∙ v 
      ≈⟨ R-sym (two-V∙ (row f0 A) u (row f0 B) v) ⟩
    Two (row f0 A) (row f0 B) V∙ Two u v
      ≈⟨ V∙-cong (first-row-four A B C D) (λ i → R-refl) ⟩ 
    row f0 (Four A B C D) V∙ Two u v ∎
    where open EqR setoid
  row-Four-Two {suc n} A B C D u v (fsuc i) with row-Four-Two {n} (λ i' j → A (fsuc i') j) (λ i' j → B (fsuc i') j) C D u v i 
  ...| induction = begin 
    Two (λ i' → A i' V∙ u R+ B i' V∙ v) (λ i' → C i' V∙ u R+ D i' V∙ v) (fsuc i) 
      ≈⟨ two-reindexing (λ i' → A i' V∙ u R+ B i' V∙ v) (λ i' → C i' V∙ u R+ D i' V∙ v) i ⟩ 
    Two (λ i' → A (fsuc i') V∙ u R+ B (fsuc i') V∙ v) (λ i' → C i' V∙ u R+ D i' V∙ v) i
      ≈⟨ induction ⟩
    row i (Four (λ i' j → A (fsuc i') j) (λ i' j → B (fsuc i') j) C D) V∙ Two u v
      ≈⟨ V∙-cong (λ i' → R-sym (Four-index-change A B C D i i')) (λ i' → R-refl) ⟩
    row (fsuc i) (Four A B C D) V∙ Two u v ∎
    where open EqR setoid

  Two-col-Four : {m n o p : ℕ} → (u : Vector m) (v : Vector p) → (A : Matrix m n) → (B : Matrix m o) → (C : Matrix p n) → (D : Matrix p o) → (j : Fin (n + o)) → Two (u VM* A V+ v VM* C) (u VM* B V+ v VM* D) j ≈ Two u v V∙ col j (Four A B C D)
  Two-col-Four {m} {zero} u v A B C D j = begin 
    u V∙ col j B R+ v V∙ col j D 
      ≈⟨ R-sym (two-V∙ u (col j B) v (col j D)) ⟩
    Two u v V∙ Two (col j B) (col j D)
      ≈⟨ R-sym (V∙-cong (λ i → R-refl) (four-empty-col A B C D j)) ⟩
    Two u v V∙ col j (Four A B C D) ∎
    where open EqR setoid
  Two-col-Four {m} {suc n} u v A B C D f0 = begin 
    u V∙ col f0 A R+ v V∙ col f0 C 
      ≈⟨ R-sym (two-V∙ u (col f0 A) v (col f0 C)) ⟩ 
    Two u v V∙ Two (col f0 A) (col f0 C)
      ≈⟨ V∙-cong (λ i → R-refl) (first-col-four A B C D) ⟩
    Two u v V∙ col f0 (Four A B C D) ∎
    where open EqR setoid
  Two-col-Four {m} {suc n} u v A B C D (fsuc j) with Two-col-Four {m} {n} u v (λ i j' → A i (fsuc j')) B (λ i j' → C i (fsuc j')) D j 
  ...| induction = begin 
    Two (λ i → u V∙ col i A R+ v V∙ col i C) (λ i → u V∙ col i B R+ v V∙ col i D) (fsuc j) 
      ≈⟨ two-reindexing (λ i → u V∙ col i A R+ v V∙ col i C) (λ i → u V∙ col i B R+ v V∙ col i D) j ⟩ 
    Two (λ i → u V∙ col (fsuc i) A R+ v V∙ col (fsuc i) C) (λ i → u V∙ col i B R+ v V∙ col i D) j
      ≈⟨ induction ⟩
    Two u v V∙ col j (Four (λ i j' → A i (fsuc j')) B (λ i j' → C i (fsuc j')) D)
      ≈⟨ V∙-cong (λ i → R-refl) (λ i' → R-sym (Four-index-change-col A B C D i' j)) ⟩
    Two u v V∙ col (fsuc j) (Four A B C D) ∎
    where open EqR setoid

  *|-Homomorphism : {s₁ s₂ : Splitting} {n₁ n₂ : ℕ} (|s₁|≡n₁ : splitSize s₁ ≡ n₁) (|s₂|≡n₂ : splitSize s₂ ≡ n₂) → (A : Mat s₁ s₂) (v : Vec s₂)
    → (Vec-to-Vector |s₁|≡n₁ (A *| v)) V≈ (Mat-to-Matrix |s₁|≡n₁ |s₂|≡n₂  A) MV* (Vec-to-Vector |s₂|≡n₂ v)
  *|-Homomorphism {one} {one} ≡-refl ≡-refl (Valiant.Concrete.Mat.Sing x) (Valiant.Concrete.Mat.one x') f0 = trans-∙ R-refl
  *|-Homomorphism {one} {one} ≡-refl ≡-refl (Valiant.Concrete.Mat.Sing x) (Valiant.Concrete.Mat.one x') (fsuc ())
  *|-Homomorphism {deeper s₁ s₂} {one} ≡-refl ≡-refl (Valiant.Concrete.Mat.CVec v) (Valiant.Concrete.Mat.one x) i = trans-∙ (|⊛-Homomorphism ≡-refl v x i)
  *|-Homomorphism {one} {deeper s₁' s₂} ≡-refl ≡-refl (Valiant.Concrete.Mat.RVec v) v' f0 = V∙-Homomorphism ≡-refl v v'
  *|-Homomorphism {one} {deeper s₁' s₂} ≡-refl ≡-refl (Valiant.Concrete.Mat.RVec v) v' (fsuc ())
  *|-Homomorphism {deeper s₁ s₂} {deeper s₁' s₂'} ≡-refl ≡-refl (Valiant.Concrete.Mat.quad A B C D) (Valiant.Concrete.Mat.two u v) i = begin 
    Two (Vec-to-Vector ≡-refl (A *| u v+ B *| v)) (Vec-to-Vector ≡-refl (C *| u v+ D *| v)) i 
      ≈⟨ Two-cong (V+-Homomorphism ≡-refl (A *| u) (B *| v)) (V+-Homomorphism ≡-refl (C *| u) (D *| v)) i ⟩
    Two (Vec-to-Vector ≡-refl (A *| u) V+ Vec-to-Vector ≡-refl (B *| v)) (Vec-to-Vector ≡-refl (C *| u) V+ Vec-to-Vector ≡-refl (D *| v)) i
      ≈⟨ Two-cong (V+-cong (*|-Homomorphism ≡-refl ≡-refl A u) (*|-Homomorphism ≡-refl ≡-refl B v)) (V+-cong (*|-Homomorphism ≡-refl ≡-refl C u) (*|-Homomorphism ≡-refl ≡-refl D v)) i ⟩
    Two (Mat-to-Matrix ≡-refl ≡-refl A MV* Vec-to-Vector ≡-refl u V+ Mat-to-Matrix ≡-refl ≡-refl B MV* Vec-to-Vector ≡-refl v)
        (Mat-to-Matrix ≡-refl ≡-refl C MV* Vec-to-Vector ≡-refl u V+ Mat-to-Matrix ≡-refl ≡-refl D MV* Vec-to-Vector ≡-refl v)
        i
        ≈⟨ row-Four-Two (Mat-to-Matrix ≡-refl ≡-refl A) (Mat-to-Matrix ≡-refl ≡-refl B) (Mat-to-Matrix ≡-refl ≡-refl C) (Mat-to-Matrix ≡-refl ≡-refl D) (Vec-to-Vector ≡-refl u) (Vec-to-Vector ≡-refl v) i ⟩ 
    row i (Four (Mat-to-Matrix ≡-refl ≡-refl A) (Mat-to-Matrix ≡-refl ≡-refl B) (Mat-to-Matrix ≡-refl ≡-refl C) (Mat-to-Matrix ≡-refl ≡-refl D)) V∙ Two (Vec-to-Vector ≡-refl u) (Vec-to-Vector ≡-refl v) ∎
    where open EqR setoid

  |*-Homomorphism : {s₁ s₂ : Splitting} {n₁ n₂ : ℕ} (|s₁|≡n₁ : splitSize s₁ ≡ n₁) (|s₂|≡n₂ : splitSize s₂ ≡ n₂) → (v : Vec s₁) (A : Mat s₁ s₂)
    → (Vec-to-Vector |s₂|≡n₂ (v |* A)) V≈  (Vec-to-Vector |s₁|≡n₁ v) VM* (Mat-to-Matrix |s₁|≡n₁ |s₂|≡n₂  A)
  |*-Homomorphism {one} {one} ≡-refl ≡-refl (Valiant.Concrete.Mat.one x) (Valiant.Concrete.Mat.Sing x') f0 = trans-∙ R-refl
  |*-Homomorphism {deeper s₁ s₂} {one} ≡-refl ≡-refl (Valiant.Concrete.Mat.two u v) (Valiant.Concrete.Mat.CVec v') f0 = V∙-Homomorphism ≡-refl (Valiant.Concrete.Mat.two u v) v'
  |*-Homomorphism {s₁} {one} ≡-refl ≡-refl v A (fsuc ())
  |*-Homomorphism {one} {deeper s₁' s₂} ≡-refl ≡-refl (Valiant.Concrete.Mat.one x) (Valiant.Concrete.Mat.RVec v) i = trans-∙ (⊛|-Homomorphism ≡-refl x v i)
  |*-Homomorphism {deeper s₁ s₂} {deeper s₁' s₂'} ≡-refl ≡-refl (Valiant.Concrete.Mat.two u v) (Valiant.Concrete.Mat.quad A B C D) i = begin 
    Two (Vec-to-Vector ≡-refl (u |* A v+ v |* C)) (Vec-to-Vector ≡-refl (u |* B v+ v |* D)) i
      ≈⟨ Two-cong (V+-Homomorphism ≡-refl (u |* A) (v |* C)) (V+-Homomorphism ≡-refl (u |* B ) (v |* D)) i ⟩
    Two (Vec-to-Vector ≡-refl (u |* A) V+ Vec-to-Vector ≡-refl (v |* C)) (Vec-to-Vector ≡-refl (u |* B) V+ Vec-to-Vector ≡-refl (v |* D)) i
      ≈⟨ Two-cong (V+-cong (|*-Homomorphism ≡-refl ≡-refl u A) (|*-Homomorphism ≡-refl ≡-refl v C)) (V+-cong (|*-Homomorphism ≡-refl ≡-refl u B) (|*-Homomorphism ≡-refl ≡-refl v D)) i ⟩
    Two (Vec-to-Vector ≡-refl u VM* Mat-to-Matrix ≡-refl ≡-refl A V+ Vec-to-Vector ≡-refl v VM* Mat-to-Matrix ≡-refl ≡-refl C) (Vec-to-Vector ≡-refl u VM* Mat-to-Matrix ≡-refl ≡-refl B V+ Vec-to-Vector ≡-refl v VM* Mat-to-Matrix ≡-refl ≡-refl D) i
      ≈⟨ Two-col-Four (Vec-to-Vector ≡-refl u) (Vec-to-Vector ≡-refl v) (Mat-to-Matrix ≡-refl ≡-refl A) (Mat-to-Matrix ≡-refl ≡-refl B) (Mat-to-Matrix ≡-refl ≡-refl C) (Mat-to-Matrix ≡-refl ≡-refl D) i ⟩
    Two (Vec-to-Vector ≡-refl u) (Vec-to-Vector ≡-refl v) V∙ col i (Four (Mat-to-Matrix ≡-refl ≡-refl A) (Mat-to-Matrix ≡-refl ≡-refl B) (Mat-to-Matrix ≡-refl ≡-refl C) (Mat-to-Matrix ≡-refl ≡-refl D)) ∎
    where open EqR setoid
  --Four : ∀ {m n o p} → Matrix m n → Matrix m o → 
  --                      Matrix p n → Matrix p o → 
  -- our-empty-row : {n o p : ℕ} (A : Matrix zero n) (B : Matrix zero o) (C : Matrix p n) (D : Matrix p o) → (i : Fin p) → row i (Four A B C D) V≈ Two (row i C) (row i D)
  


  M*-Homomorphism : {s₁ s₂ s₃ : Splitting} {n₁ n₂ n₃ : ℕ} (|s₁|≡n₁ : splitSize s₁ ≡ n₁) (|s₂|≡n₂ : splitSize s₂ ≡ n₂) (|s₃|≡n₃ : splitSize s₃ ≡ n₃) → (A : Mat s₁ s₂) (B : Mat s₂ s₃)
    → (Mat-to-Matrix |s₁|≡n₁ |s₃|≡n₃ (A m* B)) M≈ (Mat-to-Matrix |s₁|≡n₁ |s₂|≡n₂  A) M* (Mat-to-Matrix |s₂|≡n₂ |s₃|≡n₃ B)
  M*-Homomorphism {one} {one} {one} ≡-refl ≡-refl ≡-refl (Valiant.Concrete.Mat.Sing x) (Valiant.Concrete.Mat.Sing x') f0 f0 = R-sym (proj₂ R+-identity (x R* x'))
  M*-Homomorphism {one} {one} {one} ≡-refl ≡-refl ≡-refl (Valiant.Concrete.Mat.Sing x) (Valiant.Concrete.Mat.Sing x') f0 (fsuc ())
  M*-Homomorphism {one} {one} {one} ≡-refl ≡-refl ≡-refl x y (fsuc ()) j
  M*-Homomorphism {one} {deeper s₁ s₂} {one} ≡-refl ≡-refl ≡-refl (Valiant.Concrete.Mat.RVec v) (Valiant.Concrete.Mat.CVec v') f0 f0 = V∙-Homomorphism ≡-refl v v'
  M*-Homomorphism {one} {deeper s₁ s₂} {one} ≡-refl ≡-refl ≡-refl (Valiant.Concrete.Mat.RVec v) (Valiant.Concrete.Mat.CVec v') f0 (fsuc ())
  M*-Homomorphism {one} {deeper s₁ s₂} {one} ≡-refl ≡-refl ≡-refl (Valiant.Concrete.Mat.RVec v) (Valiant.Concrete.Mat.CVec v') (fsuc ()) j
  M*-Homomorphism {deeper s₁ s₂} {one} {one} ≡-refl ≡-refl ≡-refl (Valiant.Concrete.Mat.CVec v) (Valiant.Concrete.Mat.Sing x) i f0 = trans-∙ (|⊛-Homomorphism ≡-refl v x i)
  M*-Homomorphism {deeper s₁ s₂} {one} {one} ≡-refl ≡-refl ≡-refl (Valiant.Concrete.Mat.CVec v) (Valiant.Concrete.Mat.Sing x) i (fsuc ())
  M*-Homomorphism {deeper s₁ s₂} {deeper s₁' s₂'} {one} ≡-refl ≡-refl ≡-refl (Valiant.Concrete.Mat.quad A B C D) (Valiant.Concrete.Mat.CVec (Valiant.Concrete.Mat.two u v)) i f0 = begin 
    Two (Vec-to-Vector ≡-refl (A *| u v+ B *| v)) (Vec-to-Vector ≡-refl (C *| u v+ D *| v)) i
      ≈⟨ Two-cong (V+-Homomorphism ≡-refl (A *| u) (B *| v)) (V+-Homomorphism ≡-refl (C *| u) (D *| v)) i ⟩
    Two (Vec-to-Vector ≡-refl (A *| u) V+ Vec-to-Vector ≡-refl (B *| v)) (Vec-to-Vector ≡-refl (C *| u) V+ Vec-to-Vector ≡-refl (D *| v)) i
      ≈⟨ Two-cong (V+-cong (*|-Homomorphism ≡-refl ≡-refl A u) (*|-Homomorphism ≡-refl ≡-refl B v)) (V+-cong (*|-Homomorphism ≡-refl ≡-refl C u) (*|-Homomorphism ≡-refl ≡-refl D v)) i ⟩
    Two (Mat-to-Matrix ≡-refl ≡-refl A MV* Vec-to-Vector ≡-refl u V+ Mat-to-Matrix ≡-refl ≡-refl B MV* Vec-to-Vector ≡-refl v) (Mat-to-Matrix ≡-refl ≡-refl C MV* Vec-to-Vector ≡-refl u V+ Mat-to-Matrix ≡-refl ≡-refl D MV* Vec-to-Vector ≡-refl v) i
      ≈⟨ row-Four-Two (Mat-to-Matrix ≡-refl ≡-refl A) (Mat-to-Matrix ≡-refl ≡-refl B) (Mat-to-Matrix ≡-refl ≡-refl C) (Mat-to-Matrix ≡-refl ≡-refl D) (Vec-to-Vector ≡-refl u) (Vec-to-Vector ≡-refl v) i ⟩
    row i (Four (Mat-to-Matrix ≡-refl ≡-refl A) (Mat-to-Matrix ≡-refl ≡-refl B) (Mat-to-Matrix ≡-refl ≡-refl C) (Mat-to-Matrix ≡-refl ≡-refl D)) V∙ Two (Vec-to-Vector ≡-refl u) (Vec-to-Vector ≡-refl v) ∎
    where open EqR setoid
  M*-Homomorphism {deeper s₁ s₂} {deeper s₁' s₂'} {one} ≡-refl ≡-refl ≡-refl (Valiant.Concrete.Mat.quad A B C D) (Valiant.Concrete.Mat.CVec v) i (fsuc ())
  M*-Homomorphism {one} {one} {deeper s₁' s₂'} ≡-refl ≡-refl ≡-refl (Valiant.Concrete.Mat.Sing x) (Valiant.Concrete.Mat.RVec v) f0 j = trans-∙ (⊛|-Homomorphism ≡-refl x v j)
  M*-Homomorphism {one} {one} {deeper s₁' s₂'} ≡-refl ≡-refl ≡-refl (Valiant.Concrete.Mat.Sing x) (Valiant.Concrete.Mat.RVec v) (fsuc ()) j
  M*-Homomorphism {one} {deeper s₁ s₂} {deeper s₁' s₂'} ≡-refl ≡-refl ≡-refl (Valiant.Concrete.Mat.RVec (two u v)) (Valiant.Concrete.Mat.quad A B C D) f0 j = begin 
    Two (Vec-to-Vector ≡-refl (u |* A v+ v |* C)) (Vec-to-Vector ≡-refl (u |* B v+ v |* D)) j 
      ≈⟨ Two-cong (V+-Homomorphism ≡-refl (u |* A) (v |* C)) (V+-Homomorphism ≡-refl (u |* B) (v |* D)) j ⟩ 
    Two (Vec-to-Vector ≡-refl (u |* A) V+ Vec-to-Vector ≡-refl (v |* C)) (Vec-to-Vector ≡-refl (u |* B) V+ Vec-to-Vector ≡-refl (v |* D)) j
      ≈⟨ Two-cong (V+-cong (|*-Homomorphism ≡-refl ≡-refl u A) (|*-Homomorphism ≡-refl ≡-refl v C)) (V+-cong (|*-Homomorphism ≡-refl ≡-refl u B) (|*-Homomorphism ≡-refl ≡-refl v D)) j ⟩
    Two (Vec-to-Vector ≡-refl u VM* Mat-to-Matrix ≡-refl ≡-refl A V+ Vec-to-Vector ≡-refl v VM* Mat-to-Matrix ≡-refl ≡-refl C) (Vec-to-Vector ≡-refl u VM* Mat-to-Matrix ≡-refl ≡-refl B V+ Vec-to-Vector ≡-refl v VM* Mat-to-Matrix ≡-refl ≡-refl D) j
      ≈⟨ Two-col-Four (Vec-to-Vector ≡-refl u) (Vec-to-Vector ≡-refl v) (Mat-to-Matrix ≡-refl ≡-refl A) (Mat-to-Matrix ≡-refl ≡-refl B) (Mat-to-Matrix ≡-refl ≡-refl C) (Mat-to-Matrix ≡-refl ≡-refl D) j ⟩
    Two (Vec-to-Vector ≡-refl u) (Vec-to-Vector ≡-refl v) V∙ col j (Four (Mat-to-Matrix ≡-refl ≡-refl A) (Mat-to-Matrix ≡-refl ≡-refl B) (Mat-to-Matrix ≡-refl ≡-refl C) (Mat-to-Matrix ≡-refl ≡-refl D)) ∎
    where open EqR setoid
  M*-Homomorphism {one} {deeper s₁ s₂} {deeper s₁' s₂'} ≡-refl ≡-refl ≡-refl (Valiant.Concrete.Mat.RVec v) (Valiant.Concrete.Mat.quad A B C D) (fsuc ()) j
  M*-Homomorphism {deeper s₁ s₂} {one} {deeper s₁' s₂'} ≡-refl ≡-refl ≡-refl (Valiant.Concrete.Mat.CVec v) (Valiant.Concrete.Mat.RVec v') i j = trans-∙ (M⊗-Homomorphism ≡-refl ≡-refl v v' i j)
  M*-Homomorphism {deeper s₁ s₂} {deeper s₁' s₂'} {deeper s₁'' s₂''} ≡-refl ≡-refl ≡-refl (Valiant.Concrete.Mat.quad A B C D) (Valiant.Concrete.Mat.quad A' B' C' D') i j = begin 
                  Four (Mat-to-Matrix ≡-refl ≡-refl (A m* A' m+ B m* C'))
                    (Mat-to-Matrix ≡-refl ≡-refl (A m* B' m+ B m* D'))
                    (Mat-to-Matrix ≡-refl ≡-refl (C m* A' m+ D m* C'))
                    (Mat-to-Matrix ≡-refl ≡-refl (C m* B' m+ D m* D')) i j 
                    ≈⟨ Four-cong (M+-Homomorphism ≡-refl ≡-refl (A m* A') (B m* C')) (M+-Homomorphism ≡-refl ≡-refl (A m* B') (B m* D')) (M+-Homomorphism ≡-refl ≡-refl (C m* A') (D m* C')) (M+-Homomorphism ≡-refl ≡-refl (C m* B') (D m* D')) i j ⟩ --Four-cong {!M+-Homomorphism ? ? ? ?!} {!!} {!!} {!!} ⟩
                  Four (Mat-to-Matrix ≡-refl ≡-refl (A m* A') M+ Mat-to-Matrix ≡-refl ≡-refl (B m* C')) 
                       (Mat-to-Matrix ≡-refl ≡-refl (A m* B') M+ Mat-to-Matrix ≡-refl ≡-refl (B m* D')) 
                       (Mat-to-Matrix ≡-refl ≡-refl (C m* A') M+ Mat-to-Matrix ≡-refl ≡-refl (D m* C')) 
                       (Mat-to-Matrix ≡-refl ≡-refl (C m* B') M+ Mat-to-Matrix ≡-refl ≡-refl (D m* D')) i j
                    ≈⟨ Four-cong (M+-cong (M*-Homomorphism ≡-refl ≡-refl ≡-refl A A') (M*-Homomorphism ≡-refl ≡-refl ≡-refl B C')) (M+-cong (M*-Homomorphism ≡-refl ≡-refl ≡-refl A B') (M*-Homomorphism ≡-refl ≡-refl ≡-refl B D')) (M+-cong (M*-Homomorphism ≡-refl ≡-refl ≡-refl C A') (M*-Homomorphism ≡-refl ≡-refl ≡-refl D C')) (M+-cong (M*-Homomorphism ≡-refl ≡-refl ≡-refl C B') (M*-Homomorphism ≡-refl ≡-refl ≡-refl D D')) i j ⟩
                  Four
                    (Mat-to-Matrix ≡-refl ≡-refl A M* Mat-to-Matrix ≡-refl ≡-refl A' M+ Mat-to-Matrix ≡-refl ≡-refl B M* Mat-to-Matrix ≡-refl ≡-refl C')
                    (Mat-to-Matrix ≡-refl ≡-refl A M* Mat-to-Matrix ≡-refl ≡-refl B' M+ Mat-to-Matrix ≡-refl ≡-refl B M* Mat-to-Matrix ≡-refl ≡-refl D') 
                    (Mat-to-Matrix ≡-refl ≡-refl C M* Mat-to-Matrix ≡-refl ≡-refl A' M+ Mat-to-Matrix ≡-refl ≡-refl D M* Mat-to-Matrix ≡-refl ≡-refl C')
                    (Mat-to-Matrix ≡-refl ≡-refl C M* Mat-to-Matrix ≡-refl ≡-refl B' M+ Mat-to-Matrix ≡-refl ≡-refl D M* Mat-to-Matrix ≡-refl ≡-refl D')
                    i j
                    ≈⟨ row-col'' (Mat-to-Matrix ≡-refl ≡-refl A) (Mat-to-Matrix ≡-refl ≡-refl B) (Mat-to-Matrix ≡-refl ≡-refl C) (Mat-to-Matrix ≡-refl ≡-refl D) (Mat-to-Matrix ≡-refl ≡-refl A') (Mat-to-Matrix ≡-refl ≡-refl B') (Mat-to-Matrix ≡-refl ≡-refl C') (Mat-to-Matrix ≡-refl ≡-refl D') i j ⟩
                  row i (Four (Mat-to-Matrix ≡-refl ≡-refl A)
                              (Mat-to-Matrix ≡-refl ≡-refl B) 
                              (Mat-to-Matrix ≡-refl ≡-refl C)
                              (Mat-to-Matrix ≡-refl ≡-refl D))
                  V∙ 
                  col j (Four (Mat-to-Matrix ≡-refl ≡-refl A')
                              (Mat-to-Matrix ≡-refl ≡-refl B') 
                              (Mat-to-Matrix ≡-refl ≡-refl C')
                              (Mat-to-Matrix ≡-refl ≡-refl D')) ∎
    where open EqR setoid -- this proof was actually tough, because it requires _NOT_ pattern matching on i ≤? something.
        

--cong₂ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
--        (f : A → B → C) {x y u v} → x ≡ y → u ≡ v → f x u ≡ f y v
--cong₂ f refl refl = refl
--with suc (toℕ i) ≤? splitSize s₁ | suc (toℕ j) ≤? splitSize s₁''
--M*-Homomorphism {deeper s₁ s₂} {deeper s₁' s₂'} {deeper s₁'' s₂''} ≡-refl ≡-refl ≡-refl (Valiant.Concrete.Mat.quad A B C D) (Valiant.Concrete.Mat.quad A' B' C' D') i j | yes p | yes p' = {!!}


{-begin 
  Mat-to-Matrix ≡-refl ≡-refl (A m* A' m+ B m* C') (fromℕ≤ p) (fromℕ≤ p')  
    ≈⟨ M+-Homomorphism ≡-refl ≡-refl (A m* A') (B m* C') (fromℕ≤ p) (fromℕ≤ p') ⟩ 
  Mat-to-Matrix ≡-refl ≡-refl (A m* A') (fromℕ≤ p) (fromℕ≤ p') R+ Mat-to-Matrix ≡-refl ≡-refl (B m* C') (fromℕ≤ p) (fromℕ≤ p')
    ≈⟨ R+-cong (M*-Homomorphism ≡-refl ≡-refl ≡-refl A A' (fromℕ≤ p) (fromℕ≤ p')) (M*-Homomorphism ≡-refl ≡-refl ≡-refl B C' (fromℕ≤ p) (fromℕ≤ p')) ⟩
  row (fromℕ≤ p) fA   V∙   col (fromℕ≤ p') fA'     R+     row (fromℕ≤ p) fB   V∙   col (fromℕ≤ p') fC'
    ≈⟨ row-lemma' ⟩
  (_V∙_ {splitSize s₁' + splitSize s₂'}) rowiFour coljFour ∎ --row i {!!} V∙ col j {!!} ∎
  where open EqR setoid
        fA  = (Mat-to-Matrix ≡-refl ≡-refl A)
        fA' = (Mat-to-Matrix ≡-refl ≡-refl A')
        fB  = (Mat-to-Matrix ≡-refl ≡-refl B)
        fB' = (Mat-to-Matrix ≡-refl ≡-refl B')
        fC  = (Mat-to-Matrix ≡-refl ≡-refl C)
        fC' = (Mat-to-Matrix ≡-refl ≡-refl C')
        fD  = (Mat-to-Matrix ≡-refl ≡-refl D)
        fD' = (Mat-to-Matrix ≡-refl ≡-refl D')
        rowiFour : Fin (splitSize s₁' + splitSize s₂') → Carrier
        rowiFour = {!!}
        coljFour : Fin (splitSize s₁' + splitSize s₂') → Carrier
        coljFour = {!!}
        row-lemma' : row (fromℕ≤ p) fA V∙ col (fromℕ≤ p') fA' R+ row (fromℕ≤ p) fB V∙ col (fromℕ≤ p') fC'  ≈ (_V∙_ {splitSize s₁' + splitSize s₂'}) {!!} {!!}
        row-lemma' = {!!}
-}
 --R-sym (two-V∙ (row (fromℕ≤ p) fA) (col (fromℕ≤ p') fA') (row (fromℕ≤ p) fB) (col (fromℕ≤ p') fC')) ⟩
--  Two (row (fromℕ≤ p) fA) (row (fromℕ≤ p) fB) V∙ Two (col (fromℕ≤ p') fA') (col (fromℕ≤ p') fC')
--    ≈⟨ V∙-cong {u = Two (row (fromℕ≤ p) fA) (row (fromℕ≤ p) fB)} {!!} {!!} ⟩ -- R-sym (V∙-cong (λ i' → {!!}) {!!}) ⟩ --problem here?

        --pfa = _
        --pf : Fin (splitSize s₁' + splitSize s₂') → pfa
        --pf i' = {!!} --with suc (toℕ i') ≤? splitSize s₁'
        --...| aa = {!!}
{-Goal: (λ i' →
         Valiant.Abstract.Matrix.Two NAR
         (λ k → Mat-to-Matrix ≡-refl ≡-refl A (fromℕ≤ p) k)
         (λ k → Mat-to-Matrix ≡-refl ≡-refl B (fromℕ≤ p) k) i'
         | suc (toℕ i') ≤? splitSize s₁')
      V∙
      (λ i' →
         Valiant.Abstract.Matrix.Two NAR
         (λ k → Mat-to-Matrix ≡-refl ≡-refl A' k (fromℕ≤ p'))
         (λ k → Mat-to-Matrix ≡-refl ≡-refl C' k (fromℕ≤ p')) i'
         | suc (toℕ i') ≤? splitSize s₁')
      ≈
      (λ j' →
         Valiant.Abstract.Matrix.Four NAR (Mat-to-Matrix ≡-refl ≡-refl A)
         (Mat-to-Matrix ≡-refl ≡-refl B) (Mat-to-Matrix ≡-refl ≡-refl C)
         (Mat-to-Matrix ≡-refl ≡-refl D) i j'
         | yes p | suc (toℕ j') ≤? splitSize s₁')
      V∙
      (λ k →
         Valiant.Abstract.Matrix.Four NAR (Mat-to-Matrix ≡-refl ≡-refl A')
         (Mat-to-Matrix ≡-refl ≡-refl B') (Mat-to-Matrix ≡-refl ≡-refl C')
         (Mat-to-Matrix ≡-refl ≡-refl D') k j
         | suc (toℕ k) ≤? splitSize s₁' | yes p')




-}
--  row-lemma : {a b c d : ℕ} {A : Matrix a b} {B : Matrix a d} (C : Matrix c b) (D : Matrix c d) (i : Fin (a + c)) (i<m : suc (toℕ i) ≤ a) → row i (Four A B C D) V≈ Two (row (fromℕ≤ i<m) A) (row (fromℕ≤ i<m) B)
--  row-lemma {a} {b} C D i i<m j with suc (toℕ i) ≤? a | suc (toℕ j) ≤? b
--  row-lemma {A = A} C D i i<m j | yes p | yes p' = reflexive (≡-cong (λ x → A (fromℕ≤ x) (fromℕ≤ p')) (proofs-equal p i<m))
--  row-lemma {B = B} C D i i<m j | yes p | no ¬p = reflexive (≡-cong (λ x → B (fromℕ≤ x) (reduce≥ j (≤-pred (≰⇒> ¬p)))) (proofs-equal p i<m))
--  row-lemma C D i i<m j | no ¬p | _ = ⊥-elim (¬p i<m)



--row-col-mul' : {a b c d e f : ℕ} (A : Matrix a b) (B : Matrix a c) (C : Matrix d b) (D : Matrix d c ) (A' : Matrix b e) (B' : Matrix b f) (C' : Matrix c e) (D' : Matrix c f) (i : Fin (a + d)) (j : Fin (e + f)) (i<m : suc (toℕ i) ≤ a) (j<m : suc (toℕ j) ≤ e) →  row i (Four A B C D) V∙ col j (Four A' B' C' D') ≈ row (fromℕ≤ i<m) A V∙ col (fromℕ≤ j<m) A' R+ row (fromℕ≤ i<m) B V∙ col (fromℕ≤ j<m) C'
--row-col-mul' {m} {n} A B C D A' B' C' D' i j i<m j<m = begin 
--    row i (Four A B C D) V∙ col j (Four A' B' C' D') 
--      ≈⟨ V∙-cong (row-lemma C D i i<m) (col-lemma B' D' j j<m) ⟩ -- V∙-cong
--    Two (row (fromℕ≤ i<m) A) (row (fromℕ≤ i<m) B) V∙ Two (col (fromℕ≤ j<m) A') (col (fromℕ≤ j<m) C')
--      ≈⟨ two-V∙ (row (fromℕ≤ i<m) A) (col (fromℕ≤ j<m) A') (row (fromℕ≤ i<m) B) (col (fromℕ≤ j<m) C') ⟩ -- two-V∙
--    row (fromℕ≤ i<m) A V∙ col (fromℕ≤ j<m) A' R+ row (fromℕ≤ i<m) B V∙ col (fromℕ≤ j<m) C' ∎
--    where open EqR setoid







{-



M*-Homomorphism {deeper s₁ s₂} {deeper s₁' s₂'} {deeper s₁'' s₂''} ≡-refl ≡-refl ≡-refl (Valiant.Concrete.Mat.quad A B C D) (Valiant.Concrete.Mat.quad A' B' C' D') i j | yes p | no ¬p = {!i!}
M*-Homomorphism {deeper s₁ s₂} {deeper s₁' s₂'} {deeper s₁'' s₂''} ≡-refl ≡-refl ≡-refl (Valiant.Concrete.Mat.quad A B C D) (Valiant.Concrete.Mat.quad A' B' C' D') i j | no ¬p | yes p = {!!}
M*-Homomorphism {deeper s₁ s₂} {deeper s₁' s₂'} {deeper s₁'' s₂''} ≡-refl ≡-refl ≡-refl (Valiant.Concrete.Mat.quad A B C D) (Valiant.Concrete.Mat.quad A' B' C' D') i j | no ¬p | no ¬p' = {!!}-}
--row-col-mul : {a b c d e f g h : ℕ} (A : Matrix a b) (B : Matrix a c) (C : Matrix d b) (D : Matrix d c ) (A' : Matrix b b) (B' : Matrix b e) (C' : Matrix c b) (D' : Matrix c e) (i : Fin (a + d)) (j : Fin (b + e)) (i<m : suc (toℕ i) ≤ a) (j<m : suc (toℕ j) ≤ b) →  row i (Four A B C D) V∙ col j (Four A' B' C' D') ≈ row (fromℕ≤ i<m) A V∙ col (fromℕ≤ j<m) A' R+ row (fromℕ≤ i<m) B V∙ col (fromℕ≤ j<m) C'
--  row-col-mul₁ : {m n : ℕ} (A A' : Matrix m m) (B B' : Matrix m n) (C C' : Matrix n m) (D D' : Matrix n n) (i : Fin (m + n)) (j : Fin (m + n)) (i<m : suc (toℕ i) ≤ m) (j<m : suc (toℕ j) ≤ m ) →  row i (Four A B C D) V∙ col j (Four A' B' C' D') ≈ row (fromℕ≤ i<m) A V∙ col (fromℕ≤ j<m) A' R+ row (fromℕ≤ i<m) B V∙ col (fromℕ≤ j<m) C'

{-(λ k →
         Valiant.Abstract.Matrix.Four NAR (Mat-to-Matrix ≡-refl ≡-refl A)
         (Mat-to-Matrix ≡-refl ≡-refl B)
         (?11 NAR s₁ s₂ s₁'' s₂'' i j p p' s₁' s₂' A B C D A' B' C' D')
         (?12 NAR s₁ s₂ s₁'' s₂'' i j p p' s₁' s₂' A B C D A' B' C' D') i k
         | suc (toℕ i) ≤? splitSize s₁ | suc (toℕ k) ≤? splitSize s₁')
      V∙
      (λ k →
         Valiant.Abstract.Matrix.Four NAR (Mat-to-Matrix ≡-refl ≡-refl A')
         (?13 NAR s₁ s₂ s₁'' s₂'' i j p p' s₁' s₂' A B C D A' B' C' D')
         (Mat-to-Matrix ≡-refl ≡-refl C')
         (?14 NAR s₁ s₂ s₁'' s₂'' i j p p' s₁' s₂' A B C D A' B' C' D') k j   

row-lemma : {a b c d : ℕ} {A : Matrix a b} {B : Matrix a d} (C : Matrix c b) (D : Matrix c d) (i : Fin (a + c)) (i<m : suc (toℕ i) ≤ a) → row i (Four A B C D) V≈ Two (row (fromℕ≤ i<m) A) (row (fromℕ≤ i<m) B)
col-lemma : {a b c d : ℕ} {A : Matrix a b} (B : Matrix a d) {C : Matrix c b} (D : Matrix c d) (j : Fin (b + d)) (j<m : suc (toℕ j) ≤ b) → col j (Four A B C D) V≈ Two (col (fromℕ≤ j<m) A) (col (fromℕ≤ j<m) C)

         | suc (toℕ k) ≤? splitSize s₁' | suc (toℕ j) ≤? splitSize s₁'')
    --≈⟨ R-sym (row-col-mul' (Mat-to-Matrix ≡-refl ≡-refl A) (Mat-to-Matrix ≡-refl ≡-refl B) (Mat-to-Matrix ≡-refl ≡-refl C) (Mat-to-Matrix ≡-refl ≡-refl D) (Mat-to-Matrix ≡-refl ≡-refl A') (Mat-to-Matrix ≡-refl ≡-refl B') (Mat-to-Matrix ≡-refl ≡-refl C') (Mat-to-Matrix ≡-refl ≡-refl D') i j p p' ) ⟩ -- över: row (fromℕ≤ p) ∙ col (fromℕ≤ p') + 
  --row i (Four (Mat-to-Matrix ≡-refl ≡-refl A) (Mat-to-Matrix ≡-refl ≡-refl B) (Mat-to-Matrix ≡-refl ≡-refl C) (Mat-to-Matrix ≡-refl ≡-refl D)) V∙ col j (Four (Mat-to-Matrix ≡-refl ≡-refl A') (Mat-to-Matrix ≡-refl ≡-refl B') (Mat-to-Matrix ≡-refl ≡-refl C') (Mat-to-Matrix ≡-refl ≡-refl D'))
   -- ≈⟨ V∙-cong (row-lemma (Mat-to-Matrix ≡-refl ≡-refl C) (Mat-to-Matrix ≡-refl ≡-refl D) i p) (col-lemma (Mat-to-Matrix ≡-refl ≡-refl B') (Mat-to-Matrix ≡-refl ≡-refl D') j p') ⟩ -- {!row-col-mul₁ ? ? ? ? ? ? ? ? ? ? ? ? !}
   --{!!} dessa två sista är lite skumma.
--    ≡⟨ {!!} ⟩
--  {!!}


-}