-- own:
import Valiant.MatrixAlgebra.Matrix as Matrix
open import Valiant.MatrixAlgebra.ZLemmas     using (>⇒≰; less_sum_has_less) renaming (≰⇒> to z≰⇒>)
open import Valiant.MatrixAlgebra.Definitions using (toℤ; _<_)

-- standard library:
open import Algebra           using (CommutativeRing; Ring)
--open import Algebra.Structures using ()

open import Level             using () 
                              renaming (zero to zeroL)
open import Data.Vec          using (lookup)
open import Data.Nat as ℕ     using (ℕ) 
                              renaming (_+_ to _n+_; _∸_ to _n-_; zero to nzero;
                                       suc to nsuc; _⊔_ to max; _≤_ to _n≤_; 
                                       _≤?_ to _n≤?_; _<_ to _n<_; _≱_ to _n≱_ )
--open import Data.Nat.Properties using ()
open import Data.Integer as ℤ using (ℤ; _≤_; +_; _≤?_) 
                              renaming (_+_ to _z+_; _-_ to _z-_; -_ to z-_)
open import Data.Integer.Properties using (commutativeRing)

open import Data.Fin          using (Fin; _ℕ-_; inject≤; inject₁; toℕ; fromℕ) 
            --renaming (zero to zeroF; suc to sucF; pred to predF; _-_ to _f-_)

open import Relation.Nullary  using (yes; no)
open import Data.Product      using (proj₁; proj₂)

open import Data.Empty        using (⊥-elim)
open import Data.Sum          using (_⊎_) 
                              renaming (inj₁ to inj1; inj₂ to inj2;
                                                    [_,_]′ to [_,_]')
import Relation.Binary.EqReasoning as EqR         using (begin_; _≡⟨_⟩_; _≈⟨_⟩_;
                                                        _∎)

open import Relation.Binary.PropositionalEquality using (refl; sym; cong)
open Algebra.CommutativeRing commutativeRing      using () --hiding (_≈_; 0#) 
     renaming (+-identity to z+-identity; refl to zrefl; 
     -‿inverse to z-inverse; +-assoc to z+-assoc; +-comm to z+-comm)

open ℤ.≤-Reasoning            using (_≤⟨_⟩_) 
                              renaming (begin_ to ≤begin_ ; _∎ to _≤∎; 
                                       _≡⟨_⟩_ to _≤≡⟨_⟩_)

module UTriang (A : Ring zeroL zeroL) where

open Matrix A            using (Matrix; _![_,_]; rows; lookupLemma1; cols; 
                               lookupLemma2; _m*_; <_,_>; simpleOrthOrth )
open Algebra.Ring A      using (_≈_; 0#) 
                         renaming (refl to Rrefl; sym to Rsym)
open EqR (Ring.setoid A) using () 
                         renaming (begin_ to Rbegin_; _≡⟨_⟩_ to _R≡⟨_⟩_; 
                                  _≈⟨_⟩_ to _R≈⟨_⟩_; _∎ to _R∎)


-- Proof that A is upper triangular of degree d, i.e., if d > j - i, A(i,j) ≡ 0
data UTriang (d : ℤ) {rs cs : ℕ} : Matrix (nsuc rs) (nsuc cs) -> Set where
  utriang : {A : Matrix (nsuc rs) (nsuc cs)} -> 
    ((i : Fin (nsuc rs)) -> (j : Fin (nsuc cs)) -> 
    (d ≤ (toℤ j z-  toℤ i)) ⊎ (A ![ i , j ] ≈ 0#)) -> UTriang d A


--------------------------------------
-- Lemmas for proving that UTriang is preserved under multiplication
--------------------------------------

-- Column element is zero
colLemma : {n p : ℕ} (dB : ℤ) -> (B : Matrix (nsuc n) (nsuc p)) -> 
  (j : Fin (nsuc p)) -> (k : Fin (nsuc n)) ->
  ((k' : Fin (nsuc n)) -> (j' : Fin (nsuc p))                          -> 
                          (dB ≤ (toℤ j') z- (toℤ k')) ⊎ (B ![ k' , j' ] ≈ 0#))
  -> (toℤ j z- toℤ k < dB) -> (B ![ k , j ] ≈ 0#)
colLemma dB B j k f pf with f k j 
...| inj1 a = ⊥-elim (>⇒≰ pf a)
...| inj2 a = a

-- Row element is zero
rowLemma : {m n : ℕ} (dA : ℤ) -> (A : Matrix (nsuc m) (nsuc n)) -> (i : Fin (nsuc m)) -> (k : Fin (nsuc n)) -> 
  ((i' : Fin (nsuc m)) -> (k' : Fin (nsuc n))                           -> 
                          (dA ≤ (toℤ k') z- (toℤ i')) ⊎ (A ![ i' , k' ] ≈ 0#))
  -> (toℤ k z- toℤ i < dA) -> (A ![ i , k ] ≈ 0#)
rowLemma dA A i k f pf with f i k
...| inj1 a = ⊥-elim (>⇒≰ pf a)
...| inj2 a = a

-- Matrix lookup to row lookup
lookuptolookuprow : {m n : ℕ} (A : Matrix (nsuc m) (nsuc n)) -> 
  (i : Fin (nsuc m)) -> (k : Fin (nsuc n)) -> (A ![ i , k ] ≈ 0#) -> 
  (lookup k (lookup i (rows A)) ≈ 0#)
lookuptolookuprow A i k pf = Rbegin
  lookup k (lookup i (rows A)) R≡⟨ sym (lookupLemma1 A i k) ⟩
  A ![ i , k ] R≈⟨ pf ⟩
  0# R∎

-- Matrix lookup to col lookup
lookuptolookupcol : {m n : ℕ} (B : Matrix (nsuc m) (nsuc n)) -> 
  (k : Fin (nsuc m)) -> (j : Fin (nsuc n)) -> (B ![ k , j ] ≈ 0#) -> 
  (lookup k (lookup j (cols B)) ≈ 0#)
lookuptolookupcol B i k pf = Rbegin
  lookup i (lookup k (cols B)) R≡⟨ sym (lookupLemma2 B i k) ⟩
  B ![ i , k ] R≈⟨ pf ⟩
  0# R∎

-- Transforms triangular proof for A and B into triangular proof for
-- AB
zeroPf : {m n p : ℕ}
  (dA dB : ℤ)
  (A : Matrix (nsuc m) (nsuc n))
  (B : Matrix (nsuc n) (nsuc p))
  (i : Fin (nsuc m)) (j : Fin (nsuc p)) 
  -> -- Function for A
  ((iA : Fin (nsuc m)) -> (jA : Fin (nsuc n))                           -> 
                          (dA ≤ (toℤ jA) z- (toℤ iA)) ⊎ (A ![ iA , jA ] ≈ 0#))
  -> -- Function for B
  ((iB : Fin (nsuc n)) -> (jB : Fin (nsuc p))                           -> 
                          (dB ≤ (toℤ jB) z- (toℤ iB)) ⊎ (B ![ iB , jB ] ≈ 0#))
  -> -- Requirement on degree of triangularity
  (toℤ j z- toℤ i < dA z+ dB) 
  -> -- Resulting function:
  ((k : Fin (nsuc n)) -> 
   (lookup k (lookup i (rows A)) ≈ 0#) ⊎ (lookup k (lookup j (cols B)) ≈ 0#))

zeroPf dA dB A B i j fA fB pf k = 
  [
  (λ x → inj2 (lookuptolookupcol B k j (colLemma dB B j k fB x))) 
  ,
  (λ x → inj1  (lookuptolookuprow A i k (rowLemma dA A i k fA x))) 
  ]'
  (less_sum_has_less {toℤ j z- toℤ k} {toℤ k z- toℤ i} {dB} {dA} (≤begin 
    + 1 z+ ((toℤ j z- toℤ k) z+ (toℤ k z- toℤ i)) 

      ≤≡⟨ cong (λ x → + 1 z+ x) (z+-assoc (toℤ j) (z- toℤ k) 
                (toℤ k z- toℤ i)) ⟩
  
    + 1 z+ (toℤ j z+ (z- toℤ k z+ (toℤ k z- toℤ i))) 

      ≤≡⟨ sym (cong (λ x → + 1 z+ (toℤ j z+ x)) 
                       ( z+-assoc (z- toℤ k) (toℤ k) (z- toℤ i) )) ⟩
  
    + 1 z+ (toℤ j z+ ((z- toℤ k z+ toℤ k) z- toℤ i)) 

      ≤≡⟨ cong (λ x → + 1 z+ (toℤ j z+ (x z- toℤ i))) 
                                   (proj₁ z-inverse (toℤ k)) ⟩

    + 1 z+ (toℤ j z+ ((+ 0) z- toℤ i)) 

      ≤≡⟨ cong (λ x → + 1 z+ (toℤ j z+ x))
                                   (proj₁ z+-identity (z- toℤ i)) ⟩

    + 1 z+ (toℤ j z- toℤ i) 
      
      ≤⟨ pf ⟩ 
    dA z+ dB  
      ≤≡⟨ z+-comm dA dB ⟩
    
    dB z+ dA ≤∎))

-- Replace Either (not B) A with an implication
tri : {m n : ℕ} -> (A : Matrix (nsuc m) (nsuc n)) -> ℤ -> Set
tri {m} {n} A dA = ∀ (iA : Fin (nsuc m)) -> (jA : Fin (nsuc n)) -> 
                     (dA ≤ (toℤ jA) z- (toℤ iA)) ⊎ (A ![ iA , jA ] ≈ 0#)

-- The actual function for AB
triangfun : {m n p : ℕ} (dA dB : ℤ) (A : Matrix (nsuc m) (nsuc n)) 
                                    (B : Matrix (nsuc n) (nsuc p)) -> 
  (tri A dA ) -> (tri B dB ) -> (tri (A m* B) (dA z+ dB))
triangfun dA dB A B f g i j 
 with (dA z+ dB) ≤? (toℤ j z- toℤ i) | (A m* B)
... | yes pf | _ = inj1 pf
... | no  pf | C = inj2 (Rbegin 
  (A m* B) ![ i , j ] 
    
    R≈⟨ Rrefl ⟩ 
  
  < lookup i (rows A) , lookup j (cols B) > 
    
    R≈⟨ simpleOrthOrth (Matrix.sOrth (zeroPf dA dB A B i j f g (z≰⇒> pf))) ⟩ 
  
  0# R∎)

-- And the final result (probably the only thing that should be exported)!
product-preserves-triangularity : {m n p : ℕ} {A : Matrix (nsuc m) (nsuc n)} 
  {B : Matrix (nsuc n) (nsuc p)} {d₁ d₂ : ℤ} -> 
  UTriang d₁ A -> UTriang d₂ B -> UTriang (d₁ z+ d₂) (A m* B)
product-preserves-triangularity {_} {_} {_} {A} {B} {d₁} {d₂} (utriang fA) (utriang fB) = utriang (triangfun d₁ d₂ A B fA fB)
