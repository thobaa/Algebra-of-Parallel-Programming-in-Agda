%if False
\begin{code}
open import Algebra.NANRing
open import Valiant.Splitting
open import Data.Nat
module Valiant.MatAndTri (NANR : NonAssociativeNonRing) where
open NonAssociativeNonRing NANR renaming (_+_ to _R+_)
\end{code}
%endif
Mimicking the above, but using |Splitting|s as indices (the code is essentially the same, with every instance of ``|ℕ|'' replaced by ``|Splitting|''), we first define |Vec| as: \todo{probably have |Tri| above too}
\begin{code}
data Vec : Splitting → Set where
  one : (x : Carrier) → Vec one
  two : {s₁ s₂ : Splitting} → (u : Vec s₁) → (v : Vec s₂) → Vec (bin s₁ s₂)
\end{code}
We can note that where |Splitting| is a binary tree of elements of the unit type, |Vec| is instead a binary tree of |Carrier| (with elements in the leaves). We move on to defining |Mat| as:
\begin{code}
data Mat : Splitting → Splitting → Set where
  sing : (x : Carrier) → Mat one one
  rVec : {s₁ s₂ : Splitting} → (v : Vec (bin s₁ s₂)) → Mat one (bin s₁ s₂)
  cVec : {s₁ s₂ : Splitting} → (v : Vec (bin s₁ s₂)) → Mat (bin s₁ s₂) one
  quad : {r₁ r₂ c₁ c₂ : Splitting} → (A : Mat r₁ c₁) → (B : Mat r₁ c₂) → 
                                     (C : Mat r₂ c₁) → (D : Mat r₂ c₂) → Mat (bin r₁ r₂) (bin c₁ c₂)
\end{code}

The definition of the last datatype involved, |Tri| is straightforward from the subdivision made above \ref{subdivision in derivation of Valiant}. There is only one base case, that of the $1 \times 1$ zero triangle (equal to the $1 \times 1$ zero matrix when viewed as an upper triangular marix), and putting together |Tri|s is straightforward since the upper triangular matrices need to be square, now that our matrices can have any shape, and the definition guarantees that the two step splitting in \ref{two step splitting in derivation of valiant} can be done:
\begin{code}
data Tri : Splitting → Set where
  one : Tri one
  two : {s₁ s₂ : Splitting} → (U : Tri s₁) → (R : Mat s₁ s₂) → (L : Tri s₂) → Tri (bin s₁ s₂)
\end{code}
Where again, the ordering of the arguments to |two| (it takes \emph{two} |Tri|s) is such that if we introduce a line break after |Mat s₁ s₂|, and indent |Tri s₂| so it is below |Mat s₁ s₂|, they have the shape of an upper triangular matrix.

Here, we note that if we had chosen the approach with empty matrices (see \ref{empty matrices}), and correspondingly, empty |Splitting|s, we might have needed an extra constructor for triangles also \todo{think, is this true???}.


To end this section, we define addition and multiplication for |Mat| and then for |Tri|.

Addition is straightforward, since matrix addition is done pointwise, so we just recurse on the subparts, first we need to define it for |Vec|:
\begin{code}
_V+_ : {s : Splitting} → Vec s → Vec s → Vec s
one x V+ one x' = one (x R+ x')
two u v V+ two u' v' = two (u V+ u') (v V+ v')  
\end{code}
Then for |Mat|:
\begin{code}
_M+_ : {s₁ s₂ : Splitting} → Mat s₁ s₂ → Mat s₁ s₂ → Mat s₁ s₂
sing x M+ sing x' = sing (x R+ x')
rVec v M+ rVec v' = rVec (v V+ v')
cVec v M+ cVec v' = cVec (v V+ v')
quad A B C D M+ quad A' B' C' D' = quad (A M+ A') (B M+ B') (C M+ C') (D M+ D')
\end{code}
Finally for |Tri|:
\begin{code}
_T+_ : {s : Splitting} → Tri s → Tri s → Tri s
one T+ one = one
two U R L T+ two U' R' L' = two (U T+ U') (R M+ R') (L T+ L')
\end{code}

For multiplication, we need to do a bit more work (and in particular, we need to have already defined addition). The first thing to note is that if we have two matrices split into blocks, where the splitting of the columns of the first matrix equals the splitting of the rows of the second (similar to the fact that to multiply matrices $A$ and $B$, $A$ must  have as many columns as $B$ has rows), matrix multiplication works out nicely with regard to the block structures:
\begin{equation}
\begin{pmatrix}
A & B \\
C & D 
\end{pmatrix}
\begin{pmatrix}
A' & B' \\
C' & D'
\end{pmatrix}
=
\begin{pmatrix}
A A' + B C'    &    A B' + B D' \\
C A' + D C'    &    C B' + D D'
\end{pmatrix}
\end{equation}
We will use this formula to define multiplication for |Mat|. We will therefore not define multiplication for |Mat|s where the inner splittings are not equal---so our |Mat| multiplication is less general that arbitrary matrix multiplication, but it is all we need, and its simplicity is very helpful.

Nevertheless, the definition takes quite a bit of work (we need to define multiplication of |Mat s₁ s₂| and an |Mat s₂ s₃|, for all cases of |s₁|, |s₂| and |s₃|, in all, $8$ different cases). The above equation takes care of the case when |s₁| |s₂| and |s₃| are all |bin| of something. To take care of the remaining cases, we should consider vector--vector multiplication (two cases, depending on whether we are multiplying a row vector by a column vector or a column vector by a row vector), vector--matrix multiplication, matrix--vector multiplication, scalar--vector multiplication, vector--scalar multiplication, and finally scalar--scalar multiplication. All of which are different, but all can be derived from the above equation, if we allow the submatrices to have $0$ as a dimension, for example, vector--matrix multiplication is given by
\begin{align*}
  \begin{pmatrix}
    u & v
  \end{pmatrix}
  \begin{pmatrix}
    A & B \\ 
    C & D
  \end{pmatrix}
  &=
  \begin{pmatrix}
    uA + vC & uB + vD
  \end{pmatrix},
\end{align*}
and column vector--row vector multiplication (the outer product) is given by
\begin{equation}
  \begin{pmatrix}
    u \\
    v
  \end{pmatrix}
  \begin{pmatrix}
    u' & v'
  \end{pmatrix} 
= 
  \begin{pmatrix}
    uu' & uv' \\
    
  \end{pmatrix}
\end{equation}

\todo{fix these references}
\label{subdivision in derivation of Valiant}
\label{two step splitting in derivation of valiant}
