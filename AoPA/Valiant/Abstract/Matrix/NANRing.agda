open import Algebra.Structures
open import Relation.Binary using (_Preserves₂_⟶_⟶_; IsEquivalence; Reflexive; Symmetric; Transitive)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.Nat using (zero; suc)

import Relation.Binary.EqReasoning as EqR

open import Valiant.Abstract.NonAssociativeNonRing
open import Valiant.Abstract.NonAssociativeNonRing.Structure
module Valiant.Abstract.Matrix.NANRing {l₁ l₂} (NAR : NonAssociativeNonRing l₁ l₂) where

import Valiant.Abstract.Matrix as Matrix
open Matrix NAR
import Valiant.Abstract.Matrix.Operations as Operations
open Operations NAR
import Valiant.Helper.Definitions as Definitions
open Definitions NAR using (rearrangeLemma)

open import Algebra.FunctionProperties using (_DistributesOver_; _DistributesOverˡ_; _DistributesOverʳ_; Zero; LeftZero; RightZero; Associative; LeftIdentity; Commutative; Op₂)

open NonAssociativeNonRing NAR renaming (_+_ to _R+_; _≈_ to _R≈_; zero to Rzero; _*_ to _R*_)


M+-assoc : {n : _} → Associative (_M≈_ {n} {n}) _+_
M+-assoc A B C i j = begin 
  (A i j R+ B i j) R+ C i j 
    ≈⟨ NonAssociativeNonRing.+-assoc NAR (A i j) (B i j) (C i j) ⟩ 
  A i j R+ (B i j R+ C i j) ∎
  where open EqR (record { Carrier = Carrier; _≈_ = _R≈_; isEquivalence = NonAssociativeNonRing.isEquivalence NAR })
-- NonAssociativeNonRing._≈_ NAR
--    (NonAssociativeNonRing._+_ NAR (A i j) (B i j))
--    (NonAssociativeNonRing._+_ NAR (A' i j) (B' i j))
M+-cong : {n : _} → (_+_ {n} {n}) Preserves₂ _M≈_ ⟶ _M≈_ ⟶ _M≈_
M+-cong {n} {A} {A'} {B} {B'} A≈A' B≈B' i j = NonAssociativeNonRing.+-cong NAR (A≈A' i j) (B≈B' i j)

M-refl : {n : _} → Reflexive (_M≈_ {n} {n})
M-refl {n} {A} i j = NonAssociativeNonRing.refl NAR

M-sym : {n : _} → Symmetric (_M≈_ {n} {n})
M-sym {n} {A} {B} A≈B i j = NonAssociativeNonRing.sym NAR (A≈B i j)
M-trans : {n : _} → Transitive (_M≈_ {n} {n})
M-trans {n} {A} {B} {C} A≈B B≈C i j = NonAssociativeNonRing.trans NAR (A≈B i j) (B≈C i j)

M+-isEquivalence : {n : _} → IsEquivalence (_M≈_ {n} {n})
M+-isEquivalence = record { refl = M-refl; sym = M-sym; trans = M-trans }

M+-isSemigroup : {n : _} → IsSemigroup (_M≈_ {n} {n}) _+_
M+-isSemigroup = record { isEquivalence = M+-isEquivalence; assoc = M+-assoc; ∙-cong = M+-cong } 

M+-identityˡ : {n : _} → LeftIdentity (_M≈_ {n} {n}) zeroMatrix _+_
M+-identityˡ {n} A i j = NonAssociativeNonRing.identityˡ NAR (A i j)

M+-comm : {n : _} → Commutative (_M≈_ {n} {n}) _+_
M+-comm A B i j = NonAssociativeNonRing.+-comm NAR (A i j) (B i j)

M+-isCommutativeMonoid : {n : _} → IsCommutativeMonoid (_M≈_ {n} {n}) _+_ zeroMatrix
M+-isCommutativeMonoid = record { isSemigroup = M+-isSemigroup; identityˡ = M+-identityˡ; comm = M+-comm }

-- pf1 : u i' j' == v i' j'
-- vill ha: (x i ∙ (λ k → u k j)) == (y i ∙ 
-- vill ha AC = BD
∙-cong : {n : _} → (_∙_ {n}) Preserves₂ _V≈_ ⟶ _V≈_ ⟶ _R≈_
∙-cong {zero} u≈u' v≈v' = IsEquivalence.refl (NonAssociativeNonRing.isEquivalence NAR)
∙-cong {suc n} {u} {u'} {v} {v'} u≈u' v≈v' = begin 
  head u R* head v R+ (tail u ∙ tail v) 
    ≈⟨ NonAssociativeNonRing.+-cong NAR (NonAssociativeNonRing.*-cong NAR (u≈u' fzero) (v≈v' fzero)) (∙-cong (λ i → u≈u' (fsuc i)) (λ i → v≈v' (fsuc i))) ⟩
  head u' R* head v' R+ tail u' ∙ tail v' ∎
  where open EqR (record { Carrier = Carrier; _≈_ = _R≈_; isEquivalence = NonAssociativeNonRing.isEquivalence NAR })

lemma : {n : _} {A B : Matrix n n} → A M≈ B → (∀ i → A i V≈ B i)
lemma A≈B i j = A≈B i j

lemma2 : {n : _} {A B : Matrix n n} → A M≈ B → (∀ j → (λ k → A k j) V≈ (λ k → B k j))
lemma2 A≈B i j = A≈B j i

M*-cong : {n : _} → (_*_ {n} {n} {n}) Preserves₂ _M≈_ ⟶ _M≈_ ⟶ _M≈_
M*-cong {n} {A} {B} {C} {D} A≈B C≈D i j = ∙-cong (lemma A≈B i) (lemma2 C≈D j)

v-distribˡ : {n : _} → (x y z : Vector n) → (x ∙ (y V+ z)) R≈ ((x ∙ y) R+ (x ∙ z))
v-distribˡ {zero} u v w = sym (proj₁ +-identity 0#)
v-distribˡ {suc n} u v w = begin 
           (head u R* (head v R+ head w)) R+ (tail u ∙ (tail v V+ tail w))
             ≈⟨ +-cong (proj₁ distrib (head u) (head v) (head w)) (v-distribˡ (tail u) (tail v) (tail w)) ⟩ 
           (head u R* head v R+ head u R* head w) R+ ((tail u ∙ tail v) R+ (tail u ∙ tail w))
             ≈⟨ rearrangeLemma {cm = +-commutativeMonoid}  (head u R* head v) (head u R* head w) (tail u ∙ tail v) (tail u ∙ tail w) ⟩
           (head u R* head v R+ tail u ∙ tail v) R+ (head u R* head w R+ tail u ∙ tail w) ∎
  where open EqR (record { Carrier = Carrier; _≈_ = _R≈_; isEquivalence = NonAssociativeNonRing.isEquivalence NAR })

v-distribʳ : {n : _} → (x y z : Vector n) → ((y V+ z) ∙ x) R≈ ((y ∙ x) R+ (z ∙ x))
v-distribʳ {zero} u v w = sym (proj₁ +-identity 0#)
v-distribʳ {suc n} u v w = begin 
           ((head v R+ head w) R* head u) R+ ((tail v V+ tail w) ∙ tail u)
             ≈⟨ +-cong (proj₂ distrib (head u) (head v) (head w)) (v-distribʳ (tail u) (tail v) (tail w)) ⟩ 
           (head v R* head u R+ head w R* head u) R+ ((tail v ∙ tail u) R+ (tail w ∙ tail u)) 
             ≈⟨ rearrangeLemma {cm = +-commutativeMonoid} (head v R* head u) (head w R* head u) (tail v ∙ tail u) (tail w ∙ tail u) ⟩ 
           (head v R* head u R+ tail v ∙ tail u) R+ (head w R* head u R+ tail w ∙ tail u) ∎
  where open EqR (record { Carrier = Carrier; _≈_ = _R≈_; isEquivalence = NonAssociativeNonRing.isEquivalence NAR })


M-distribˡ : {n : _} → _DistributesOverˡ_ (_M≈_ {n} {n}) _*_ _+_
M-distribˡ A B C i j = v-distribˡ (A i) (λ k → B k j) (λ k → C k j)

M-distribʳ : {n : _} → _DistributesOverʳ_ (_M≈_ {n} {n}) _*_ _+_
M-distribʳ A B C i j = v-distribʳ (λ k → A k j) (B i) (C i)

M-distrib : {n : _} → _DistributesOver_ (_M≈_ {n} {n}) _*_ _+_
M-distrib = M-distribˡ , M-distribʳ

v-leftZero : ∀ {n} v → (zeroVector {n}) ∙ v R≈ 0#
v-leftZero {zero} v = refl
v-leftZero {suc n} v = begin 
           0# R* head v R+ zeroVector ∙ tail v 
             ≈⟨ +-cong (proj₁ Rzero (head v)) (v-leftZero (tail v)) ⟩
           0# R+ 0#
             ≈⟨ proj₁ +-identity 0# ⟩ 
           0# ∎
  where open EqR (record { Carrier = Carrier; _≈_ = _R≈_; isEquivalence = NonAssociativeNonRing.isEquivalence NAR })

v-rightZero : ∀ {n} v → v ∙ (zeroVector {n}) R≈ 0#
v-rightZero {zero} v = refl
v-rightZero {suc n} v = begin 
            head v R* 0# R+ tail v ∙ zeroVector 
              ≈⟨ +-cong (proj₂ Rzero (head v)) (v-rightZero (tail v)) ⟩
            0# R+ 0#
              ≈⟨ proj₁ +-identity 0# ⟩
            0# ∎
  where open EqR (record { Carrier = Carrier; _≈_ = _R≈_; isEquivalence = NonAssociativeNonRing.isEquivalence NAR })

M-leftZero : {n : _} → LeftZero (_M≈_ {n} {n}) zeroMatrix _*_
M-leftZero A i j = v-leftZero (λ i' → A i' j)

M-rightZero : {n : _} → RightZero (_M≈_ {n} {n}) zeroMatrix _*_
M-rightZero A i j = v-rightZero (A i)


M-zero : {n : _} → Zero (_M≈_ {n} {n}) zeroMatrix _*_
M-zero = M-leftZero , M-rightZero

-- Proof that square Matrices form a NonAssociativeNonRing:
MisNonAssociativeNonRing : {n : _} → IsNonAssociativeNonRing (_M≈_ {n} {n}) _+_ _*_ zeroMatrix
MisNonAssociativeNonRing = record 
  {
    +-isCommutativeMonoid = M+-isCommutativeMonoid;
    *-cong = M*-cong;
    distrib = M-distrib;
    zero = M-zero 
  }

nonAssociativeNonRing : {n : _} → NonAssociativeNonRing _ _
nonAssociativeNonRing {n} = record {
                          Carrier = Matrix n n;
                          _≈_ = _M≈_;
                          _+_ = _+_;
                          _*_ = _*_;
                          0# = zeroMatrix;
                          isNonAssociativeNonRing = MisNonAssociativeNonRing }