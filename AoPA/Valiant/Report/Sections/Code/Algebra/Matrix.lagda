\label{Matrices}
In Agda, we will only define the type of a matrix over the nonassociative semiring. For simplicity, and to allow us to avoid adding the nonassociative semiring as an argument to every function and proposition, we decide to parametrize the module we place the definition of a matrix in by a nonassociative semiring, and open the nonassociative semiring, renaming things so they start with ``|R-|'' to make it clear when we are referring to the concepts in the underlying nonassociative semiring:
\begin{spec}
module Matrix (NaSr : NonassociativeSemiring) where
open NonassociativeSemiring NaSr 
  renaming  (  _+_         to  _R+_
            ;  _*_         to  _R*_
            ;  _≈_         to  _R≈_
            ;  zero        to  R-zero
            ;  +-cong      to  R+-cong
            ;  +-comm      to  R+-comm
            ;  +-identity  to  R+-identity
            ;  refl        to  R-refl
            ;  +-commutativeMonoid  to R+-CM
            )
\end{spec}
%if False
\begin{code}
open import Algebra.NANRing
open import Data.Nat
open import Data.Fin
module Algebra.Matrix (NaSr : NonassociativeSemiring) where
infix 4 _M≈_
\end{code}
%endif 
%if False
\begin{code}
open NonassociativeSemiring NaSr public renaming (_+_ to _R+_; _*_ to _R*_; _≈_ to _R≈_; zero to R-zero; +-comm to R+-comm; +-identity to R+-identity; refl to R-refl;  +-commutativeMonoid  to R+-CM;  +-cong      to  R+-cong)
\end{code}
%endif
If we didn't open the record, instead of, for example |a R+ b| for adding |a| to |b|, we would have to write the much less readable
\begin{spec}
(NonassociativeSemiring._+_ NaSr) a b
\end{spec}
Now we to define our matrix type in Agda as
\begin{code}
Matrix : ℕ → ℕ → Set
Matrix m n = Fin m → Fin n → R
\end{code}

As with the algebraic structures previously, we want to be able to say that two matrices are equal.
We will thus define matrix equality, which we denote by |_M≈_| to disambiguate it from the regular equality. It should take two matrices to the proposition that they are equal, and two matrices |A| and |B| are equal if for all indices |i| and |j|, |A i j| and |B i j| are equal.
\begin{code}
_M≈_ : {m n : ℕ} → Matrix m n → Matrix m n → Set
A M≈ B = ∀ i j → A i j R≈ B i j
\end{code}

Wealso define the zero matrix. It should be a matrix whose elements are all equal to the zero in the nonassociative semiring.
\begin{code}
zeroMatrix : {m n : ℕ} → Matrix m n
zeroMatrix i j = R0
\end{code}
