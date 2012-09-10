-- own:
import Matrix 
open import ZLemmas renaming (≰⇒> to z≰⇒>)
open import Definitions -- using (Either; toℤ; _<_)

-- standard library:
open import Algebra -- using (CommutativeRing)
open import Algebra.Structures

open import Level renaming (zero to zz ; suc to ss)
open import Data.Vec
open import Data.Nat as ℕ renaming (_+_ to _n+_; _∸_ to _n-_; zero to nzero; 
                                    suc to nsuc; _⊔_ to max; _≤_ to _n≤_; 
                                    _≤?_ to _n≤?_; _<_ to _n<_; _≱_ to _n≱_ )
open import Data.Nat.Properties
open import Data.Integer  as ℤ renaming (_+_ to _z+_; _-_ to _z-_; -_ to z-_)
open import Data.Integer.Properties

open import Data.Fin using (Fin; _ℕ-_; inject≤; inject₁; toℕ; fromℕ) 
            renaming (zero to fzero; suc to fsuc; pred to fpred; _-_ to _f-_)

open import Relation.Nullary using (Dec; yes; no)
open import Data.Product using (proj₁; proj₂)

open import Data.Empty using (⊥-elim)

import Relation.Binary.EqReasoning as EqR

open import Relation.Binary.PropositionalEquality 
  renaming (refl to eqrefl; sym to eqsym; cong to eqcong; cong₂ to eqcong₂)

open CommutativeRing commutativeRing hiding (_≈_; 0#) 
     renaming (+-identity to z+-identity; refl to zrefl; 
     -‿inverse to z-inverse; +-assoc to z+-assoc; +-comm to z+-comm)

open ℤ.≤-Reasoning renaming (begin_ to start_ ; _∎ to _□; _≡⟨_⟩_ to _≡⟨_⟩'_)

module UTriang (A : Ring zz zz) where

open Matrix A 
open Ring A renaming (sym to Rsym)
open EqR (Ring.setoid A)


-- Proof that A is upper triangular of degree d, i.e., if d > j - i, A(i,j) ≡ 0
data UTriang (d : ℤ) {rs cs : ℕ} : Matrix (nsuc rs) (nsuc cs) -> Set where
  utriang : {A : Matrix (nsuc rs) (nsuc cs)} -> 
    ((i : Fin (nsuc rs)) -> (j : Fin (nsuc cs)) -> 
    Either (d ≤ (toℤ j z-  toℤ i)) (A ![ i , j ] ≈ 0#)) -> UTriang d A


--------------------------------------
-- Lemmas for proving that UTriang is preserved under multiplication
--------------------------------------

-- Column element is zero
colLemma : {n p : ℕ} (dB : ℤ) -> (B : Matrix (nsuc n) (nsuc p)) -> 
  (j : Fin (nsuc p)) -> (k : Fin (nsuc n)) ->
  ((k' : Fin (nsuc n)) -> (j' : Fin (nsuc p))                          -> 
                          Either (dB ≤ (toℤ j') z- (toℤ k')) 
                                 (B ![ k' , j' ] ≈ 0#))                ->
  (toℤ j z- toℤ k < dB) -> (B ![ k , j ] ≈ 0#)
colLemma dB B j k f pf with f k j 
...| left a = ⊥-elim (>⇒≰ pf a)
...| right a = a

-- Row element is zero
rowLemma : {m n : ℕ} (dA : ℤ) -> (A : Matrix (nsuc m) (nsuc n)) -> (i : Fin (nsuc m)) -> (k : Fin (nsuc n)) -> 
  ((i' : Fin (nsuc m)) -> (k' : Fin (nsuc n))                           -> 
                          Either (dA ≤ (toℤ k') z- (toℤ i'))  
                                 (A ![ i' , k' ] ≈ 0#))                 ->
  (toℤ k z- toℤ i < dA) -> (A ![ i , k ] ≈ 0#)
rowLemma dA A i k f pf with f i k
...| left a = ⊥-elim (>⇒≰ pf a)
...| right a = a

-- Matrix lookup to row lookup
lookuptolookuprow : {m n : ℕ} (A : Matrix (nsuc m) (nsuc n)) -> 
  (i : Fin (nsuc m)) -> (k : Fin (nsuc n)) -> (A ![ i , k ] ≈ 0#) -> 
  (lookup k (lookup i (rows A)) ≈ 0#)
lookuptolookuprow A i k pf = begin
  lookup k (lookup i (rows A)) ≡⟨ eqsym (lookupLemma1 A i k) ⟩
  A ![ i , k ] ≈⟨ pf ⟩
  0# ∎

-- Matrix lookup to col lookup
lookuptolookupcol : {m n : ℕ} (B : Matrix (nsuc m) (nsuc n)) -> 
  (k : Fin (nsuc m)) -> (j : Fin (nsuc n)) -> (B ![ k , j ] ≈ 0#) -> 
  (lookup k (lookup j (cols B)) ≈ 0#)
lookuptolookupcol B i k pf = begin
  lookup i (lookup k (cols B)) ≡⟨ eqsym (lookupLemma2 B i k) ⟩
  B ![ i , k ] ≈⟨ pf ⟩
  0# ∎

-- Transforms triangular proof for A and B into triangular proof for
-- AB
zeroPf : {m n p : ℕ}
  (dA dB : ℤ)
  (A : Matrix (nsuc m) (nsuc n))
  (B : Matrix (nsuc n) (nsuc p))
  (i : Fin (nsuc m)) (j : Fin (nsuc p)) 
  -> -- Function for A
  ((iA : Fin (nsuc m)) -> (jA : Fin (nsuc n))                           -> 
                          Either (dA ≤ (toℤ jA) z- (toℤ iA))  
                                 (A ![ iA , jA ] ≈ 0#))
  -> -- Function for B
  ((iB : Fin (nsuc n)) -> (jB : Fin (nsuc p))                           -> 
                          Either (dB ≤ (toℤ jB) z- (toℤ iB)) 
                                 (B ![ iB , jB ] ≈ 0#))  
  -> -- Requirement on degree of triangularity
  (toℤ j z- toℤ i < dA z+ dB) 
  -> -- Resulting function:
  ((k : Fin (nsuc n)) -> 
   Either (lookup k (lookup i (rows A)) ≈ 0#) 
   (lookup k (lookup j (cols B)) ≈ 0#))

zeroPf dA dB A B i j fA fB pf k = fromEither 
  (λ x → right (lookuptolookupcol B k j (colLemma dB B j k fB x))) 
  (λ x → left  (lookuptolookuprow A i k (rowLemma dA A i k fA x))) 
  (less_sum_has_less {toℤ j z- toℤ k} {toℤ k z- toℤ i} {dB} {dA} (start 
    + 1 z+ ((toℤ j z- toℤ k) z+ (toℤ k z- toℤ i)) 

      ≡⟨ eqcong (λ x → + 1 z+ x) (z+-assoc (toℤ j) (z- toℤ k) 
                (toℤ k z- toℤ i)) ⟩'
  
    + 1 z+ (toℤ j z+ (z- toℤ k z+ (toℤ k z- toℤ i))) 

      ≡⟨ eqsym (eqcong (λ x → + 1 z+ (toℤ j z+ x)) 
                       ( z+-assoc (z- toℤ k) (toℤ k) (z- toℤ i) )) ⟩'
  
    + 1 z+ (toℤ j z+ ((z- toℤ k z+ toℤ k) z- toℤ i)) 

      ≡⟨ eqcong (λ x → + 1 z+ (toℤ j z+ (x z- toℤ i))) 
                                   (proj₁ z-inverse (toℤ k)) ⟩'

    + 1 z+ (toℤ j z+ ((+ 0) z- toℤ i)) 

      ≡⟨ eqcong (λ x → + 1 z+ (toℤ j z+ x))
                                   (proj₁ z+-identity (z- toℤ i)) ⟩'

    + 1 z+ (toℤ j z- toℤ i) 
      
      ≤⟨ pf ⟩ dA z+ dB  ≡⟨ z+-comm dA dB ⟩'
    
    dB z+ dA □))

-- Replace Either (not B) A with an implication
tri : {m n : ℕ} -> (A : Matrix (nsuc m) (nsuc n)) -> ℤ -> Set
tri {m} {n} A dA = ∀ (iA : Fin (nsuc m)) -> (jA : Fin (nsuc n)) -> 
                     Either (dA ≤ (toℤ jA) z- (toℤ iA)) (A ![ iA , jA ] ≈ 0#)

-- The actual function for AB
triangfun : {m n p : ℕ} (dA dB : ℤ) (A : Matrix (nsuc m) (nsuc n)) 
                                    (B : Matrix (nsuc n) (nsuc p)) -> 
  (tri A dA ) -> (tri B dB ) -> (tri (A m* B) (dA z+ dB))
triangfun dA dB A B f g i j 
 with (dA z+ dB) ≤? (toℤ j z- toℤ i) | (A m* B)
... | yes pf | _ = left pf
... | no  pf | C = right (begin 
  (A m* B) ![ i , j ] 
    
    ≈⟨ refl ⟩ 
  
  < lookup i (rows A) , lookup j (cols B) > 
    
    ≈⟨ simpleOrthOrth (Matrix.sOrth (zeroPf dA dB A B i j f g (z≰⇒> pf))) ⟩ 
  
  0# ∎)

-- And the final result (probably the only thing that should be exported)!
product-preserves-triangularity : {m n p : ℕ} {A : Matrix (nsuc m) (nsuc n)} 
  {B : Matrix (nsuc n) (nsuc p)} {d₁ d₂ : ℤ} -> 
  UTriang d₁ A -> UTriang d₂ B -> UTriang (d₁ z+ d₂) (A m* B)
product-preserves-triangularity {_} {_} {_} {A} {B} {d₁} {d₂} (utriang fA) (utriang fB) = utriang (triangfun d₁ d₂ A B fA fB)
