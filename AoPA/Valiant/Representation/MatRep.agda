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
open Valiant.Concrete.Mat.Operations NAR using (_|⊛_; _⊛|_) renaming (_+_ to _m+_; _*_ to _m*_; _⊕_ to _v+_; _∙_ to _v∙_; _⊛_ to _v⊗_)
open Valiant.Abstract.Matrix NAR

open Valiant.Abstract.Matrix.Operations NAR using (_M≈_; _V≈_; _V+_; _Vs*_; _sV*_; trans-∙) renaming (_+_ to _M+_;_*_ to _M*_; _∙_ to _V∙_; _⊗_ to _V⊗_)
open Valiant.Concrete.Tri.Equalities NAR using (_m≈_; _v≈_)


open NonAssociativeNonRing NAR renaming (_+_ to _R+_; _*_ to _R*_; zero to R-zero; refl to R-refl; sym to R-sym; +-identity to R+-identity; +-cong to R+-cong; +-assoc to R+-assoc)

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
  Vec-to-Vector-cong {one} ≡-refl (Valiant.Concrete.Tri.Equalities.one-eq x≈y) f0 = x≈y
  Vec-to-Vector-cong {one} ≡-refl (Valiant.Concrete.Tri.Equalities.one-eq x≈y) (fsuc ())
  Vec-to-Vector-cong {deeper s₁ s₂} ≡-refl (Valiant.Concrete.Tri.Equalities.two-eq u₁≈v₁ u₂≈v₂) i with suc (toℕ i) ≤? splitSize s₁
  Vec-to-Vector-cong {deeper s₁ s₂} ≡-refl (Valiant.Concrete.Tri.Equalities.two-eq u₁≈v₁ u₂≈v₂) i | yes p = Vec-to-Vector-cong ≡-refl u₁≈v₁ (fromℕ≤ p)
  Vec-to-Vector-cong {deeper s₁ s₂} ≡-refl (Valiant.Concrete.Tri.Equalities.two-eq u₁≈v₁ u₂≈v₂) i | no ¬p = Vec-to-Vector-cong ≡-refl u₂≈v₂ (reduce≥ i (≤-pred (≰⇒> ¬p)))


  Mat-to-Matrix-cong : {s₁ s₂ : Splitting} {n₁ n₂ : ℕ} → 
                       {A B : Mat s₁ s₂} → (|s₁|≡n₁ : splitSize s₁ ≡ n₁) → (|s₂|≡n₂ : splitSize s₂ ≡ n₂) → 
                          A m≈ B → Mat-to-Matrix |s₁|≡n₁ |s₂|≡n₂ A M≈ Mat-to-Matrix |s₁|≡n₁ |s₂|≡n₂ B
  Mat-to-Matrix-cong {one} {one} ≡-refl ≡-refl (Valiant.Concrete.Tri.Equalities.Sing-eq x≈y) f0 f0 = x≈y
  Mat-to-Matrix-cong {one} {one} ≡-refl ≡-refl (Valiant.Concrete.Tri.Equalities.Sing-eq x≈y) f0 (fsuc ())
  Mat-to-Matrix-cong {one} {one} ≡-refl ≡-refl (Valiant.Concrete.Tri.Equalities.Sing-eq x≈y) (fsuc ()) j
  Mat-to-Matrix-cong {deeper s₁ s₂} {one} ≡-refl ≡-refl (Valiant.Concrete.Tri.Equalities.CVec-eq u≈v) i f0 = Vec-to-Vector-cong ≡-refl u≈v i
  Mat-to-Matrix-cong {deeper s₁ s₂} {one} ≡-refl ≡-refl (Valiant.Concrete.Tri.Equalities.CVec-eq u≈v) i (fsuc ())
  Mat-to-Matrix-cong {one} {deeper s₁' s₂} ≡-refl ≡-refl (Valiant.Concrete.Tri.Equalities.RVec-eq u≈v) f0 j = Vec-to-Vector-cong ≡-refl u≈v j
  Mat-to-Matrix-cong {one} {deeper s₁' s₂} ≡-refl ≡-refl (Valiant.Concrete.Tri.Equalities.RVec-eq u≈v) (fsuc ()) j
  Mat-to-Matrix-cong {deeper s₁ s₂} {deeper s₁' s₂'} ≡-refl ≡-refl (Valiant.Concrete.Tri.Equalities.quad-eq A₁≈A₂ B₁≈B₂ C₁≈C₂ D₁≈D₂) i j with suc (toℕ i) ≤? splitSize s₁ | suc (toℕ j) ≤? splitSize s₁'
  Mat-to-Matrix-cong {deeper s₁ s₂} {deeper s₁' s₂'} ≡-refl ≡-refl (Valiant.Concrete.Tri.Equalities.quad-eq A₁≈A₂ B₁≈B₂ C₁≈C₂ D₁≈D₂) i j | yes p | yes p' = Mat-to-Matrix-cong ≡-refl ≡-refl A₁≈A₂ (fromℕ≤ p) (fromℕ≤ p')
  Mat-to-Matrix-cong {deeper s₁ s₂} {deeper s₁' s₂'} ≡-refl ≡-refl (Valiant.Concrete.Tri.Equalities.quad-eq A₁≈A₂ B₁≈B₂ C₁≈C₂ D₁≈D₂) i j | yes p | no ¬p = Mat-to-Matrix-cong ≡-refl ≡-refl B₁≈B₂ (fromℕ≤ p) (reduce≥ j (≤-pred (≰⇒> ¬p)))
  Mat-to-Matrix-cong {deeper s₁ s₂} {deeper s₁' s₂'} ≡-refl ≡-refl (Valiant.Concrete.Tri.Equalities.quad-eq A₁≈A₂ B₁≈B₂ C₁≈C₂ D₁≈D₂) i j | no ¬p | yes p = Mat-to-Matrix-cong ≡-refl ≡-refl C₁≈C₂ (reduce≥ i (≤-pred (≰⇒> ¬p))) (fromℕ≤ p)
  Mat-to-Matrix-cong {deeper s₁ s₂} {deeper s₁' s₂'} ≡-refl ≡-refl (Valiant.Concrete.Tri.Equalities.quad-eq A₁≈A₂ B₁≈B₂ C₁≈C₂ D₁≈D₂) i j | no ¬p | no ¬p' = Mat-to-Matrix-cong ≡-refl ≡-refl D₁≈D₂ (reduce≥ i (≤-pred (≰⇒> ¬p))) (reduce≥ j (≤-pred (≰⇒> ¬p')))


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

V∙-Homomorphism : {s : Splitting} {n : ℕ} (|s|≡n : splitSize s ≡ n) → (u v : Vec s) → u v∙ v ≈ Vec-to-Vector |s|≡n u V∙ Vec-to-Vector |s|≡n v
V∙-Homomorphism {one} ≡-refl u v = {!!}
V∙-Homomorphism {deeper s₁ s₂} ≡-refl u v = {!!}

abstract 
  |⊛-Homomorphism : {s : Splitting} {n : ℕ} (|s|≡n : splitSize s ≡ n) → (v : Vec s) (x : Carrier) → (Vec-to-Vector |s|≡n (v |⊛ x)) V≈ Vec-to-Vector |s|≡n v Vs* x
  |⊛-Homomorphism {one} ≡-refl (Valiant.Concrete.Mat.one x) x' f0 = R-refl
  |⊛-Homomorphism {one} ≡-refl (Valiant.Concrete.Mat.one x) x' (fsuc ())
  |⊛-Homomorphism {deeper s₁ s₂} ≡-refl (Valiant.Concrete.Mat.two u v) x i with suc (toℕ i) ≤? splitSize s₁
  |⊛-Homomorphism {deeper s₁ s₂} ≡-refl (Valiant.Concrete.Mat.two u v) x i | yes p = |⊛-Homomorphism ≡-refl u x (fromℕ≤ p)
  |⊛-Homomorphism {deeper s₁ s₂} ≡-refl (Valiant.Concrete.Mat.two u v) x i | no ¬p = |⊛-Homomorphism ≡-refl v x (reduce≥ i (≤-pred (≰⇒> ¬p)))

⊛|-Homomorphism : {s : Splitting} {n : ℕ} (|s|≡n : splitSize s ≡ n) → (x : Carrier) (v : Vec s) → (Vec-to-Vector |s|≡n (x ⊛| v)) V≈ x sV* Vec-to-Vector |s|≡n v
⊛|-Homomorphism = {!!}

-- lemma about row-column multiplication

abstract
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

two-V∙ : {m n : ℕ} (u u' : Vector m) (v v' : Vector n) → Two u v V∙ Two u' v' ≈ u V∙ u' R+ v V∙ v'
two-V∙ = {!!}

--four-V∙ : {m n : ℕ} (u u' : Matrix m) (v v' : Vector n) → row  V∙ u' R+ v V∙ v' ≈ 
V∙-cong : {m : ℕ} {u u' v v' : Vector m} → u V≈ u' → v V≈ v' → u V∙ v ≈ u' V∙ v'
V∙-cong = {!!}

-- this might not have been proved before, as Matrix m n is not a ring.
M+-cong : {m n : ℕ} {A A' B B' : Matrix m n} → A M≈ A' → B M≈ B' → A M+ B M≈ A' M+ B'
M+-cong A≈A' B≈B' i j = R+-cong (A≈A' i j) (B≈B' i j)

abstract
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


row-col : {m n o p q r : ℕ} (A : Matrix m n) (B : Matrix m o) (C : Matrix p n) (D : Matrix p o) (A' : Matrix n q) (B' : Matrix n r) (C' : Matrix o q) (D' : Matrix o r) → (i : Fin (m + p)) → (j : Fin (q + r)) → Four (A M* A' M+ B M* C') (A M* B' M+ B M* D') (C M* A' M+ D M* C')
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
          {!!}
            ≈⟨ {!row-col' {m} {n} ? ? ? ? ? ? ? ? ? ?!} ⟩
          {!!} ∎
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

-- funktion som returnerar Four med "with"
--Four : ∀ {m n o p} → Matrix m n → Matrix m o → 
--                      Matrix p n → Matrix p o → 
Four-cong : {m n o p : ℕ} {a a' : Matrix m n} {b b' : Matrix m o} {c c' : Matrix p n} {d d' : Matrix p o} → a M≈ a' → b M≈ b' → c M≈ c' → d M≈ d' → Four a b c d M≈ Four a' b' c' d'
Four-cong {m} {n} a≈a' b≈b' c≈c' d≈d' i j with suc (toℕ i) ≤? m | suc (toℕ j) ≤? n
Four-cong a≈a' b≈b' c≈c' d≈d' i j | yes p | yes p' = a≈a' (fromℕ≤ p) (fromℕ≤ p')
Four-cong a≈a' b≈b' c≈c' d≈d' i j | yes p' | no ¬p = b≈b' (fromℕ≤ p') (reduce≥ j (≤-pred (≰⇒> ¬p)))
Four-cong a≈a' b≈b' c≈c' d≈d' i j | no ¬p | yes p' = c≈c' (reduce≥ i (≤-pred (≰⇒> ¬p))) (fromℕ≤ p')
Four-cong a≈a' b≈b' c≈c' d≈d' i j | no ¬p | no ¬p' = d≈d' (reduce≥ i (≤-pred (≰⇒> ¬p))) (reduce≥ j (≤-pred (≰⇒> ¬p')))

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
M*-Homomorphism {deeper s₁ s₂} {deeper s₁' s₂'} {one} ≡-refl ≡-refl ≡-refl (Valiant.Concrete.Mat.quad A B C D) (Valiant.Concrete.Mat.CVec v) i f0 = {!!}
M*-Homomorphism {deeper s₁ s₂} {deeper s₁' s₂'} {one} ≡-refl ≡-refl ≡-refl (Valiant.Concrete.Mat.quad A B C D) (Valiant.Concrete.Mat.CVec v) i (fsuc ())
M*-Homomorphism {one} {one} {deeper s₁' s₂'} ≡-refl ≡-refl ≡-refl (Valiant.Concrete.Mat.Sing x) (Valiant.Concrete.Mat.RVec v) f0 j = trans-∙ (⊛|-Homomorphism ≡-refl x v j)
M*-Homomorphism {one} {one} {deeper s₁' s₂'} ≡-refl ≡-refl ≡-refl (Valiant.Concrete.Mat.Sing x) (Valiant.Concrete.Mat.RVec v) (fsuc ()) j
M*-Homomorphism {one} {deeper s₁ s₂} {deeper s₁' s₂'} ≡-refl ≡-refl ≡-refl (Valiant.Concrete.Mat.RVec v) (Valiant.Concrete.Mat.quad A B C D) f0 j = {!t!}
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
                  ≈⟨ row-col (Mat-to-Matrix ≡-refl ≡-refl A) (Mat-to-Matrix ≡-refl ≡-refl B) (Mat-to-Matrix ≡-refl ≡-refl C) (Mat-to-Matrix ≡-refl ≡-refl D) (Mat-to-Matrix ≡-refl ≡-refl A') (Mat-to-Matrix ≡-refl ≡-refl B') (Mat-to-Matrix ≡-refl ≡-refl C') (Mat-to-Matrix ≡-refl ≡-refl D') i j ⟩
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