open import Valiant.Abstract.NonAssociativeNonRing
open import Valiant.Abstract.NonAssociativeNonRing.Structure

module Valiant.Abstract.Triangle.NANRing {l₁ l₂} (NAR : NonAssociativeNonRing l₁ l₂) where

import Valiant.Abstract.Triangle.Operations
open Valiant.Abstract.Triangle.Operations NAR

TisNonAssociativeNonRing : {n : _} → IsNonAssociativeNonRing (_T≈_ {n} {n}) _+_ _*_ zeroMatrix
TisNonAssociativeNonRing = record 
  {
    +-isCommutativeMonoid = M+-isCommutativeMonoid;
    *-cong = M*-cong;
    distrib = M-distrib;
    zero = M-zero 
  }