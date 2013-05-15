
\todo{Fix formatting of 0\#}

In Agda, we will only define the type of a matrix over the \nanring. For simplicity, and to allow us to avoid adding the \nanring as an argument to every functino and proposition, we decide to parametrize the module the definition of the matrix by a nanring. Assuming that we have placed the definition of the \nanring in \verb?NANRing.agda?, we import it: 
\begin{spec}
open import NANRing.agda
\end{spec}
%if False
\begin{code}
open import Algebra.NANRing
open import Data.Nat
open import Data.Fin
module Algebra.Matrix (NAR : NonAssociativeNonRing) where
\end{code}
%endif
Then, if the current module is placed in \verb?Matrix.lagda?, we write:
\begin{spec}
module Matrix (NAR : NonAssociativeNonRing) where
\end{spec}
The part |(NAR : NonAssociativeNonRing)| is an argument to the module matrix.

We open the record |NonAssociativeNonRing| with |NAR| so that we will be able to use the definitions in the ring easily, and rename things so that they do not clash with concepts we will define for the matrices (and also to help us figure out what operation we are using):
%if False
\begin{code}
open NonAssociativeNonRing NAR public renaming (_+_ to _R+_; _*_ to _R*_; _≈_ to _R≈_; zero to R-zero; +-comm to R+-comm)
\end{code}
%endif
\begin{spec}
open NonAssociativeNonRing NAR renaming (_+_ to _R+_; _*_ to _R*_; _≈_ to _R≈_; zero to R-zero)
\end{spec}
If we didn't open the record, instead of, for example |a R+ b| for adding |a| to |b|, we would have to write
\begin{spec}
(NonAssociativeNonRing._+_ NAR) a b
\end{spec}
Now we are ready to define our matrix type in Agda:
\begin{code}
Matrix : (m n : ℕ) → Set
Matrix m n = Fin m → Fin n → R
\end{code}

As with the algebraic structures previously, we would like a way to speak of equality among matrices. First, we make a helpful definition of the equality in the \nanring |NAR|:
We will thus define matrix equality, which we denote by |_M≈_| to disambiguate it from the regular equality (in the library it is called |_≈_|, since it is in its own module \todo{make sure that it really is called |_≈_| in the library}). It should take two matrices to the proposition that they are equal, and two matrices |A| and |B| are equal if for all indices |i| and |j|, |A i j| and |B i j| are equal.
\begin{code}
infix 4 _M≈_
_M≈_ : {m n : ℕ} → Matrix m n → Matrix m n → Set
A M≈ B = ∀ i j → A i j R≈ B i j
\end{code}

We end by defining the zero matrix. It should be a matrix whose elements are all equal to the zero element of the \nanring.
\begin{code}
zeroMatrix : {m n : ℕ} → Matrix m n
zeroMatrix i j = R0
\end{code}
