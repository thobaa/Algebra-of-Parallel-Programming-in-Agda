%if False
\begin{code}
import Algebra.Matrix
import Algebra.MatrixOperations
open import Data.Fin using (Fin)
open import Algebra.Monoid
open import Algebra.NANRing
module Algebra.MatrixProof (NAR : NonAssociativeNonRing) where
--open NonAssociativeNonRing NAR renaming (_+_ to _R+_; _*_ to _R*_; _≈_ to _R≈_)

open Algebra.Matrix NAR
open Algebra.MatrixOperations NAR
\end{code}
%endif
%As before, we put the proof in a parametrised module, so we always have access to our base \nanring called |NAR|.
We begin to prove that they form a commutative monoid. This is done by giving an element of the type
\begin{spec}
IsCommutativeMonoid (_M≈_ {m} {n}) 
\end{spec}
We give this type the name |M+-isCommutativeMonoid|, and expand the record datatype:
\begin{code}
M+-isCommutativeMonoid : ∀ {m n} → IsCommutativeMonoid (_M≈_ {m} {n}) _M+_ zeroMatrix
\end{code}
\begin{spec}
M+-isCommutativeMonoid = record { isMonoid = {!!}; comm = {!!} }
\end{spec}
We prove only part of the |comm|-axiom, the proofs involved in proving |isMonoid| are similar. We begin by writing the type:
\begin{code}
M+-comm : ∀ {m n} → (x y : Matrix m n) → x M+ y M≈ y M+ x
\end{code}
\begin{spec}
M+-comm x y = {!!}
\end{spec}
Then, we remember the definitions of |_M+_| and |_M≈_|, and note that they are both pointwise operations, in fact, Agda sees this as well, if we position the cursor in the hole above and press \verb?C-c C-,?, Agda tells us that the goal is of type:
\begin{spec}
Goal: (i : Fin .m) (j : Fin .n) →
      NonAssociativeNonRing._≈_ NAR
      (NonAssociativeNonRing._+_ NAR (x i j) (y i j))
      (NonAssociativeNonRing._+_ NAR (y i j) (x i j))
\end{spec}
which after cleaning up is:
\begin{spec}
Goal:  (i : Fin m) (j : Fin n) →
       (x i j) R+ (y i j) R≈ (y i j) R+ (x i j))
\end{spec}
Hence, we should provide function that takes |i : Fin m| and |j : Fin n| to a proof that the ring elements |x i j| and |y i j| commute. But this is exactly what |R-comm| is.
\begin{code}
M+-comm x y = λ i j → R+-comm (x i j) (y i j)
\end{code}
%if False
\begin{code}
postulate cheat0 : ∀ {m n} → IsMonoid (_M≈_ {m} {n}) _M+_ zeroMatrix
M+-isCommutativeMonoid = record { isMonoid = cheat0; comm = M+-comm }
\end{code}
%endif

The proof is an element of the type
\begin{code}
M-isNonAssociativeNonRing : ∀ {n} → IsNonAssociativeNonRing (_M≈_ {n} {n}) (_M+_) _M*_ zeroMatrix
M-isNonAssociativeNonRing = record {
                                   +-isCommutativeMonoid = M+-isCommutativeMonoid;
                                   *-cong = {!!};
                                   distrib = {!!};
                                   zero = {!!} }
\end{code}
\todo{DO PROOF AND WRITE STUFF!}
