%if False
\begin{code}
open import Data.Nat
open import Data.Product using (proj₁)
open import Data.Fin using (Fin; toℕ) renaming (zero to fzero; suc to fsuc)
open import Algebra.NANRing
open import Algebra.Monoid
module Algebra.Triangle (NAR : NonAssociativeNonRing) where

import Algebra.Matrix
open Algebra.Matrix NAR
import Algebra.MatrixOperations
open Algebra.MatrixOperations NAR

--open NonAssociativeNonRing NAR

\end{code}
%endif

In Agda, there are two obvious ways to define a triangular matrix. The first way would be to use records, where a triangular matix is a matrix along with a proof that it is triangular. The second way would be to use functions that take two arguments and return a ring element, but where the second argument must be strictly greater than the first. We show one difference between the two approaches in Figure \ref{Figure:TriangularMatrixOrTriangle}
\begin{figure}
  \centering
  \missingfigure{draw figure of two matrices, one with zeros below diagonal, one with nothing (or stars or somethign)\label{Figure:TriangularMatrixOrTriangle}}
\end{figure}

We choose the first approach here, because it will make it possible to use the majority of the work from when we proved that matrices form a \nanring to show that triangular matrices also form a \nanring (or a ring, if their elements form a ring), under the obvious multiplication, addition and equality. The only problem we will have is proving that the multiplication is closed. Here it is important repeat that by triangular, we mean upper triangular (although everything would work equally well if we used it to mean lower triangular, as long as it doesn't include both upper and lower) if both upper and lower triangular matrices were allowed, we would not get a ring, , since it is well known that any matrix can be factorized as a product of a lower and an upper triangular matrix.

One additional reason for not choosing the second approach is that inequalities among |Fin| are not very nice \todo{expand on this paragraph}.

Thus we define triangular matrices of triangularity |d| (and give them the name |Triangle|):
%if False
\begin{spec}
infix 6 _-_
_-_ : {n : ℕ} → Fin n → Fin n → Fin n
fzero - j = fzero
fsuc i - fzero = fsuc i
fsuc i - fsuc i' = raise (i - i')
  where raise : {n : ℕ} → Fin n → Fin (suc n)
        raise fzero = fzero
        raise (fsuc i0) = fsuc (raise i0)
infix 5 _≤_
data _≤_ : {n : ℕ} → Fin n → Fin n →  Set where
  fz≤i  : {n : ℕ} {i : Fin (suc n)} → fzero ≤ i
  fs≤fs : {n : ℕ} {i j : Fin (suc n)} → i ≤ j → fsuc i ≤ fsuc j
\end{spec}
%endif
\begin{code}
record Triangle (n : ℕ) : Set where --(d : Fin n) : Set where
  field 
    mat : Matrix n n
    tri : (i j : Fin n) → toℕ i ≤ toℕ j → mat i j R≈ R0
\end{code}

We also define two |Triangle|s to be equal if they have the same underlying matrix, since the proof is only there to ensure us that they are actually upper triangular.\todo{do we actually want arbitrary triangularity? Pros: makes going from sum to different spec easier, do we want that? Cons: trickier definition. probably not}
\begin{code}
_T≈_ : {n : ℕ} → Triangle n → Triangle n → Set
A T≈ B = Triangle.mat A M≈ Triangle.mat B
\end{code}

Now, we go on to define addition and multiplication of triangles. We apply matrix addition on their matrices and modify their proofs. For addition, the proof modification is straightforward:
\begin{code}
_T+_ : {n : ℕ} → Triangle n → Triangle n → Triangle n
A T+ B = record 
  { mat = Triangle.mat A M+ Triangle.mat B
  ; tri = λ i j i≤j → 0′+0″≈0 +-commutativeMonoid (Triangle.tri A i j i≤j) (Triangle.tri B i j i≤j) }
\end{code}

For multiplication, the proof modification required is a bit more complicated, and requires a lemma related to dot-products.
\begin{code}
_T*_ : {n : ℕ} → Triangle n → Triangle n → Triangle n
A T* B = record 
  { mat = Triangle.mat A M* Triangle.mat B
  ; tri = {!!} }
\end{code}
