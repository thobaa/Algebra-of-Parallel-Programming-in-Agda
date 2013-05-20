%if False
\begin{code}
open import Algebra.NANRing
--open import Agda.List1
--open import Agda.List2 hiding (_*_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
import Algebra.Matrix
module Algebra.MatrixOperations (NaSr : NonassociativeSemiring) where
infix 5 _M+_ 
infixl 7 _M*_
open Algebra.Matrix NaSr
\end{code}
%endif
To define the addition in Agda is straightforward: 
\begin{code}
_M+_ : {m n : ℕ} → Matrix m n → Matrix m n → Matrix m n
A M+ B = λ i j → A i j R+ B i j
\end{code}

To define multiplication, on the other hand, we consider the alternative definition of the product as the matrix formed by taking scalar products between the rows of $A$ and the columns of $B$:
\begin{equation}\label{Matrix-mul}
  (AB)_{i j} = \vec{a_i} \cdot \vec{b_j},
\end{equation}
where $\vec{a_i}$ is the $i$th row vector of $A$ and $\vec{b_j}$ is the $j$th column vector of $B$.

For this, we define the datatype |Vector| of a (mathematical) vector, represented as a function from indices to elements of a nonassociative semiring:
\begin{code}
Vector : ℕ → Set
Vector n = Fin n → R
\end{code}
We define the dot product by pattern matching on the length of the vector, making local definitions of |head| and |tail| for clarity:
\begin{code}
_∙_ : {n : ℕ} → Vector n → Vector n → R
_∙_  {zero}   u   v = R0
_∙_  {suc n}  u   v = (head u R* head v) R+ (tail u ∙ tail v)
  where  head    : {n : ℕ} → Vector (suc n) → R
         head v  = v fzero
         tail    : {n : ℕ} → Vector (suc n) → Vector n
         tail v  = λ i → v (fsuc i)
\end{code}
With it, we define matrix multiplication (in Agda, we can't use |AB| or |A B| for matrix multiplication since juxtaposition means function application):
\begin{code}
_M*_ : {m n p : ℕ} → Matrix m n → Matrix n p → Matrix m p
(A M* B) i j = row i A ∙ col j B
  where  row : {m n : ℕ} → Fin m → Matrix m n → Vector n
         row i A = λ k → A i k
         col : {m n : ℕ} → Fin n → Matrix m n → Vector m
         col j B = λ k → B k j
\end{code}
Here, Agda helps us in making sure that the definition is correct. If we start from the fact that the product of a $m \times n$ matrix and an $n \times p$ matrix is an $m \times p$ matrix, Agda more or less makes sure that our vectors are row vectors for |A| and column vectors for |B|.
Alternatively, if we by writing down the formula \eqref{Matrix-mul} as the definition, Agda forces |A| to have as many rows as |B| has columns.
