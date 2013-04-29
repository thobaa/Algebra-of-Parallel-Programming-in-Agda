open import Valiant.Abstract.NonAssociativeNonRing
open import Valiant.Abstract.NonAssociativeNonRing.Structure
open import Algebra.Structures
open import Relation.Binary using (IsEquivalence)

open import Data.Product using (_,_; proj₁; proj₂)

module Valiant.Abstract.Triangle.NANRing {l₁ l₂} (NAR : NonAssociativeNonRing l₁ l₂) where

import Valiant.Abstract.Triangle
open Valiant.Abstract.Triangle NAR
import Valiant.Abstract.Triangle.Operations
open Valiant.Abstract.Triangle.Operations NAR

import Valiant.Abstract.Matrix.NANRing hiding (nonAssociativeNonRing)
open Valiant.Abstract.Matrix.NANRing NAR


-- basically, lift everything (we do it by filling in the non-record stuff and give names to the records)!

TisEquivalence : {n : _} → IsEquivalence (_T≈_ {n})
TisEquivalence {n} = record 
  { 
  refl = refl; 
  sym = sym; 
  trans = trans 
  }
  where open IsNonAssociativeNonRing (MisNonAssociativeNonRing {n})

T+-isSemigroup : {n : _} → IsSemigroup (_T≈_ {n}) _T+_
T+-isSemigroup {n} = record 
  { 
  isEquivalence = TisEquivalence; 
  assoc = λ A B C → +-assoc (Triangle.matrix A) (Triangle.matrix B) (Triangle.matrix C); 
  ∙-cong = +-cong
  }
  where open IsNonAssociativeNonRing (MisNonAssociativeNonRing {n})

T+-isCommutativeMonoid : {n : _} → IsCommutativeMonoid (_T≈_ {n}) _T+_ zeroTriangle
T+-isCommutativeMonoid {n} = record 
  { 
  isSemigroup = T+-isSemigroup; 
  identityˡ = λ A → identityˡ (Triangle.matrix A); 
  comm = λ A B → +-comm (Triangle.matrix A) (Triangle.matrix B) 
  }
  where open IsNonAssociativeNonRing (MisNonAssociativeNonRing {n})

TisNonAssociativeNonRing : {n : _} → IsNonAssociativeNonRing (_T≈_  {n}) _T+_ _T*_ zeroTriangle
TisNonAssociativeNonRing {n} = record 
  {
  +-isCommutativeMonoid = T+-isCommutativeMonoid;
  *-cong = *-cong;
  distrib = (λ A B C → proj₁ distrib (Triangle.matrix A) (Triangle.matrix B) (Triangle.matrix C)) , (λ A B C → proj₂ distrib (Triangle.matrix A) (Triangle.matrix B) (Triangle.matrix C));
  zero = (λ A → proj₁ zero (Triangle.matrix A)) , (λ A → proj₂ zero (Triangle.matrix A))  
  }
  where open IsNonAssociativeNonRing (MisNonAssociativeNonRing {n})

nonAssociativeNonRing : {n : _} → NonAssociativeNonRing _ _
nonAssociativeNonRing {n} = record {
                          Carrier = Triangle n;
                          _≈_ = _T≈_;
                          _+_ = _T+_;
                          _*_ = _T*_;
                          0# = zeroTriangle;
                          isNonAssociativeNonRing = TisNonAssociativeNonRing }