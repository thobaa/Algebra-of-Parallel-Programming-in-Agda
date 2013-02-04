-- this module contains proofs related to representation of Matrix as Mat
open import Data.Nat
open import Data.Fin using (Fin; fromℕ; fromℕ≤; toℕ;  raise; reduce≥) 
                     renaming (zero to f0; suc to fsuc)


open import Valiant.Abstract.NonAssociativeNonRing

module Valiant.Representation.MatRepProofs {l₁ l₂} (NAR : NonAssociativeNonRing l₁ l₂) where


import Valiant.Concrete.Mat as Mat
import Valiant.Abstract.Matrix as Matrix

import Valiant.Representation.MatRep as MatRep

open Mat NAR
open Matrix NAR

open MatRep NAR

-- ska kunna ta en matris -> mat -> matris, ska vara id.
-- eller mat -> matris -> mat, behöver inte vara id, 
-- splitMat (matToSplit A) == A
{-splitToMat∘matToSplit≡id' : (m n : ℕ) (i : Fin (suc m)) (j : Fin (suc n)) → (A : Matrix (suc m) (suc n)) → splitToMat (matToSplit A) (outFin i) (outFin j) ≡  A i j 
splitToMat∘matToSplit≡id' m n i j A = begin 
  splitToMat (matToSplit A) (outFin i) (outFin j) 
    ≡⟨ splitToMat∘matToSplit≡id m n (outFin i) (outFin j) A ⟩ 
  A (injFin (outFin i)) (injFin (outFin j)) 
    ≡⟨ cong₂ A injFin∘outFin≡id injFin∘outFin≡id ⟩ 
  A i j ∎-}