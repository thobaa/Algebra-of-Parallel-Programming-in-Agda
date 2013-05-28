%if False
\begin{code}
import Algebra.Matrix
import Algebra.MatrixOperations
open import Data.Fin using (Fin)
open import Data.Nat
open import Data.Product
open import Algebra.Monoid
open import Algebra.NANRing
module Algebra.MatrixProof (NaSr : NonassociativeSemiring) where


open Algebra.Matrix NaSr
open Algebra.MatrixOperations NaSr
\end{code}
%endif
We begin to prove that they form a commutative monoid. This is done by giving an element |M+-isCommutativeMonoid| of type 
\begin{code}
M+-isCommutativeMonoid :  ∀ {m n} → IsCommutativeMonoid 
                          (_M≈_ {m} {n}) _M+_ zeroMatrix
\end{code}
We need to supply the implicit arguments to |_M≈_| to make Agda understand what size of matrices the proposition concerns.
To define this element, we need to give a proof that it is a monoid, and a proof that it is commutative. Here, we only include the proof of the |comm|-axiom, the proofs involved in proving |isMonoid| are similar to it. The proof should be an element of type
\begin{code}
M+-comm : ∀ {m n} → (x y : Matrix m n) → x M+ y M≈ y M+ x
\end{code}
Then, we recall the definitions of |_M+_| and |_M≈_|, in particular that they are both pointwise operations. In fact, Agda tells us that the type reduces to:
\begin{spec}
(i : Fin .m) (j : Fin .n) →  
NonassociativeSemiring._≈_ NaSr
(NonassociativeSemiring._+_ NaSr (x i j) (y i j))
(NonassociativeSemiring._+_ NaSr (y i j) (x i j))
\end{spec}
which is the same as:
\begin{spec}
(i : Fin m) (j : Fin n) →
(x i j) R+ (y i j) R≈ (y i j) R+ (x i j))
\end{spec}
Hence, we should provide function that takes |i : Fin m| and |j : Fin n| to a proof that the nonassociative semiring elements |x i j| and |y i j| commute. But |R-comm| proves that any two elements of |R| commute, so we define |M+-comm| as:
\begin{code}
M+-comm x y = λ i j → R+-comm (x i j) (y i j)
\end{code}
%if False
\begin{code}
postulate 
  cheat0 : ∀ {m n} → IsMonoid (_M≈_ {m} {n}) _M+_ zeroMatrix
  cheat1 : ∀ {n} → {x x' y y' : Fin n → Fin n → NonassociativeSemiring.R NaSr} →
                     ((i j : Fin n) →
                      NonassociativeSemiring._≈_ NaSr (x i j) (x' i j)) →
                     ((i j : Fin n) →
                      NonassociativeSemiring._≈_ NaSr (y i j) (y' i j)) →
                     (i j : Fin n) →
                     NonassociativeSemiring._≈_ NaSr (x i ∙ (λ k → y k j))
                     (x' i ∙ (λ k → y' k j))
  cheat2 : ∀ {n} → Σ
                     ((x y z : Fin n → Fin n → NonassociativeSemiring.R NaSr)
                      (i j : Fin n) →
                      NonassociativeSemiring._≈_ NaSr
                      (x i ∙ (λ k → NonassociativeSemiring._+_ NaSr (y k j) (z k j)))
                      (NonassociativeSemiring._+_ NaSr (x i ∙ (λ k → y k j))
                       (x i ∙ (λ k → z k j))))
                     (λ x →
                        (x' y z : Fin n → Fin n → NonassociativeSemiring.R NaSr)
                        (i j : Fin n) →
                        NonassociativeSemiring._≈_ NaSr
                        ((λ j' → NonassociativeSemiring._+_ NaSr (y i j') (z i j')) ∙
                         (λ k → x' k j))
                        (NonassociativeSemiring._+_ NaSr (y i ∙ (λ k → x' k j))
                         (z i ∙ (λ k → x' k j))))
  cheat3 : ∀ {n} → (x : Matrix n n) → (x M* zeroMatrix {n} {n}) M≈ zeroMatrix


M+-isCommutativeMonoid = record { isMonoid = cheat0; comm = M+-comm }
\end{code}
%endif

To prove that the square matrices form a nonassociative semiring, we need to give an element |M-isNonassociativeSemiring| of type
\begin{code}
M-isNonassociativeSemiring : ∀ {n} → IsNonassociativeSemiring 
                             (_M≈_ {n}) (_M+_) _M*_ zeroMatrix
\end{code}
which includes giving proofs that matrices with addition form a commutative monoid, along with proofs that matrix multiplication respects matrix equality and distributes over matrix addition, and that |zeroMatrix| is a zero element. The last part consists of two conjuncts. We prove the left one here.

To prove this, we want to give an element:
\begin{code}
M-zeroˡ : ∀ {n} →  (x : Matrix n n) → 
                   zeroMatrix {n} {n} M* x M≈ zeroMatrix
\end{code}
Agda tells us that the type of |M-zeroˡ {n}| reduces to
\begin{spec}
(x : Matrix n n) (i j : Fin n) → (zeroVector ∙ col j x ) R≈ R0
\end{spec}
where
\begin{code}
zeroVector : {n : ℕ} → Vector n
zeroVector _ = R0
\end{code}
We prove that |zeroVector ∙ v ≈ R0| for any |v| by induction on the lenght. The only interesting fact that appears is that the type of |∙-zero {suc n} {v}| reduces to 
\begin{spec}
(R0 R* head v) R+ (zeroVector ∙ tail v) R≈ R0
\end{spec}
so we apply our lemma from Section \ref{e'e''e}:
\begin{code}
∙-zero : ∀ {n v} → zeroVector {n} ∙ v R≈ R0
∙-zero {zero}       = R-refl
∙-zero {suc n} {v}  = e'∙e''≈e R+-CM  (proj₁ R-zero (head v)) 
                                      (∙-zero {n})
\end{code}
%Having to rearrange things like this happens very often, and might imply that there is a slight incompatibility between the definition of |_∙_| and the proposition |
%if False
\begin{code}
  where
        head : {n : _} → Vector (suc n) → R
        head v = v Data.Fin.zero
        tail : {n : _} → Vector (suc n) → Vector n
        tail v = λ x → v (Data.Fin.suc x)

M-isNonassociativeSemiring = record {
                                   +-isCommutativeMonoid = M+-isCommutativeMonoid;
                                   *-cong = cheat1;
                                   distrib = cheat2;
                                   zero = M-zeroˡ , cheat3 }
\end{code}
%endif
Then we define
\begin{code}
M-zeroˡ {n} x i j = ∙-zero {n}
\end{code}

Finally, we give a name to the matrix nonassociative semiring, so we can supply it as an element of type |NonassociativeSemiring| (of course, we do the same with commutative monoid):
\begin{code}
M-nonassociativeSemiring : ∀ {n} → NonassociativeSemiring
M-nonassociativeSemiring {n} = record {
                             isNonassociativeSemiring = M-isNonassociativeSemiring {n}}
\end{code}
