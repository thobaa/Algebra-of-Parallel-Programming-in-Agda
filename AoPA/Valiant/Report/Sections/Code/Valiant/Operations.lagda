%if False
\begin{code}
open import Algebra.NANRing
open import Valiant.Splitting
open import Data.Nat
open import Data.Product renaming (_×_ to _∧_)
open import Data.Unit
module Valiant.Operations (NANR : NonAssociativeNonRing) where
import Valiant.MatAndTri
open Valiant.MatAndTri NANR
--open NonAssociativeNonRing NANR renaming (_+_ to _R+_; _*_ to _R*_; 0# to R0; _≈_ to _R≈_)

infix 7 _m*_ 
infix 7 _vm*_
infix 7 _mv*_
infixl 6 _m+_ 
infix 6 _v+_
infix 7 _tm*_
infix 4 _m≈_
infix 7 _mt*_
infix 7 _vt*_
infix 7 _tv*_
infix 4 _v≈_
infix 7 _t*_
infix 6 _t+_
infix 4 _t≈_

\end{code}
%endif
\subsubsection{Operations on our datatypes}
Now, we will define operations, addition, multiplication and equality, for our datatypes, |Vec|, |Mat| and |Tri|. We only need the operations for |Tri|, but, for example, to multiply two |Tri|s, we need to be able to multiply the rectangular parts with triangles, and to do this, in turn, we need to be able to multiply two matrices, which requires the ability to multiply vectors.

Addition is straightforward, since matrix addition is done pointwise, so we just recurse on the subparts, first we need to define it for |Vec|:
\begin{code}
_v+_ : {s : Splitting} → Vec s → Vec s → Vec s
one x v+ one x' = one (x R+ x')
two u v v+ two u' v' = two (u v+ u') (v v+ v')  
\end{code}
Then for |Mat|:
\begin{code}
_m+_ : {s₁ s₂ : Splitting} → Mat s₁ s₂ → Mat s₁ s₂ → Mat s₁ s₂
sing x m+ sing x' = sing (x R+ x')
rVec v m+ rVec v' = rVec (v v+ v')
cVec v m+ cVec v' = cVec (v v+ v')
quad A B C D m+ quad A' B' C' D' = quad (A m+ A') (B m+ B') (C m+ C') (D m+ D')
\end{code}
Finally for |Tri|:
\begin{code}
_t+_ : {s : Splitting} → Tri s → Tri s → Tri s
one t+ one = one
two U R L t+ two U' R' L' = two (U t+ U') (R m+ R') (L t+ L')
\end{code}
The overall structure used above when defining addition for the different datatypes is fairly typical of what needs to be done when defining something that is essentially a lifting of an operation (as it is for the abstract matrix \ref{abstract-matrix}).

For multiplication, which is not simply a lifting, we need to do a bit more work (and in particular, we need to have already defined addition). The first thing to note is that if we have two matrices split into blocks, where the splitting of the columns of the first matrix equals the splitting of the rows of the second (similar to the fact that to multiply matrices $A$ and $B$, $A$ must  have as many columns as $B$ has rows), matrix multiplication works out nicely with regard to the block structures:
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
  (
    u' , v'
  ) 
= 
  \begin{pmatrix}
    uu' & uv' \\
    vu' & vv'
  \end{pmatrix}
\end{equation}

We now begin defining these multiplications in Agda. There is some dependency between them, for example, to define outer product, we need both kinds of scalar--vector multiplication (although we don't need anything to define the dot product). We hence begin with the simplest kinds of multiplication, first scalar--vector mutliplication:
\begin{code}
_sv*_ : {s : Splitting} → R → Vec s → Vec s
x sv* one x' = one (x R* x')
x sv* two u v = two (x sv* u) (x sv* v) 
\end{code}
and then vector--scalar multiplication:
\begin{code}
_vs*_ : {s : Splitting} → Vec s → R → Vec s
one x vs* x' = one (x R* x')
two u v vs* x = two (u vs* x) (v vs* x)
\end{code}
Then we move on to the dot product:
\begin{code}
_∙_ : {s : Splitting} → Vec s → Vec s → R
one x ∙ one x' = x R* x'
two u v ∙ two u' v' = u ∙ u' R+ v ∙ v'
\end{code}
next, we move on to scalar--matrix and matrix--scalar multiplication (the definition of which we leave out since it is essentially the same as scalar--matrix multiplication):
\begin{code}
_sm*_ : {s₁ s₂ : Splitting} → R → Mat s₁ s₂ → Mat s₁ s₂
x sm* sing x' = sing (x R* x')
x sm* rVec v = rVec (x sv* v)
x sm* cVec v = cVec (x sv* v)
x sm* quad A B C D = quad (x sm* A) (x sm* B) (x sm* C) (x sm* D)

_ms*_ : {s₁ s₂ : Splitting} → Mat s₁ s₂ → R → Mat s₁ s₂
\end{code}
%if False
\begin{code}
sing x ms* x' = sing (x R* x')
rVec v ms* x = rVec (v vs* x)
cVec v ms* x = cVec (v vs* x)
quad A B C D ms* x = quad (A ms* x) (B ms* x) (C ms* x) (D ms* x)
\end{code}
%endif
Next we define the outer product:
\begin{code}
_⊗_ : {s₁ s₂ : Splitting} → Vec s₁ → Vec s₂ → Mat s₁ s₂
one x ⊗ one x' = sing (x R* x')
one x ⊗ two u v = rVec (two (x sv* u) (x sv* v))
two u v ⊗ one x = cVec (two (u vs* x) (v vs* x))
two u v ⊗ two u' v' = quad (u ⊗ u') (u ⊗ v') (v ⊗ u') (v ⊗ v')
\end{code}
and note that we could have defined the multiplications by a single element vector, using |sv*| on one level higher: 
\begin{spec}
one x ⊗ two u v = rVec (x sv* (two u v))
\end{spec}
but either way, we need to pattern match on the vector to tell if it is |one x'| or |two u v|, since we need to use different constructors for the matrix (and using a smart multiplication function doesn't help much, since we need to do the same thing when proving things anyway). Next, we give the types of vector--matrix and matrix--vector multiplication (but leave out the implementation):
\begin{code}
_vm*_ : {s₁ s₂ : Splitting} → Vec s₁ → Mat s₁ s₂ → Vec s₂

_mv*_ : {s₁ s₂ : Splitting} → Mat s₁ s₂ → Vec s₂ → Vec s₁
\end{code}
%if False
\begin{code}
one x vm* sing x' = one (x R* x')
one x vm* rVec v =  x sv* v
two u v vm* cVec (two u' v') = one (two u v ∙ two u' v')
two u v vm* quad A B C D = two (u vm* A v+ v vm* C) (u vm* B v+ v vm* D)
sing x mv* one x' = one (x R* x')
rVec (two u v) mv* two u' v' = one (two u v ∙ two u' v')
cVec v mv* one x = v vs* x
quad A B C D mv* two u v = two (A mv* u v+ B mv* v) (C mv* u v+ D mv* v)
\end{code}
%endif
Finally, we can define matrix multiplication:
\begin{code}
_m*_ : {s₁ s₂ s₃ : Splitting} → Mat s₁ s₂ → Mat s₂ s₃ → Mat s₁ s₃
sing x m* sing x' = sing (x R* x')
sing x m* rVec v = rVec (x sv* v)
rVec v m* cVec v' = sing (v ∙ v')
rVec (two u v) m* quad A B C D = rVec (two (u vm* A v+ v vm* C) (u vm* B v+ v vm* D))
cVec v m* sing x = cVec (v vs* x)
cVec v m* rVec v' = v ⊗ v' --
quad A B C D m* cVec (two u v) = cVec (two (A mv* u v+ B mv* v) (C mv* u v+ D mv* v))
quad A B C D m* quad A' B' C' D' = quad (A m* A' m+ B m* C') (A m* B' m+ B m* D') (C m* A' m+ D m* C') (C m* B' m+ D m* D')
\end{code}

To define triangle multiplication is a lot simpler, since we only need to consider one index. However, we need matrix multiplication in its full generality, because in general, the |Splitting| involved is not a balanced binary tree, and hence, the row splitting and the column splitting differs (the case |two U R L| doesn't require that |U| and |L| have the same splitting, since the constructor |bin| takes two splittings).

We also need to define multiplication between |Vec| and |Tri| and between |Mat| and |Tri|, all of which are straight-forward to define:
\begin{code}
_vt*_ : {s : Splitting} → Vec s → Tri s → Vec s
_tv*_ : {s : Splitting} → Tri s → Vec s → Vec s
_mt*_ : {s₁ s₂ : Splitting} → Mat s₁ s₂ → Tri s₂ → Mat s₁ s₂
_tm*_ : {s₁ s₂ : Splitting} → Tri s₁ → Mat s₁ s₂ → Mat s₁ s₂
\end{code}
%if False
\begin{code}
one x vt* one = one R0
two u v vt* two U R L = two (u vt* U) (u vm* R v+ v vt* L)
one tv* one x = one R0
two U R L tv* two u v = two (U tv* u v+ R mv* v) (L tv* v)
sing x mt* one = sing R0
rVec (two u v) mt* two U R L = rVec (two (u vt* U) (u vm* R v+ v vt* L))
cVec v mt* one = cVec zeroVec
quad A B C D mt* two U R L = quad (A mt* U) (A m* R m+ B mt* L) (C mt* U) (C m* R m+ D mt* L)
one tm* sing x = sing R0
one tm* rVec v = rVec zeroVec
two U R L tm* cVec (two u v) = cVec (two (U tv* u v+ R mv* v) (L tv* v))
two U R L tm* quad A B C D = quad (U tm* A m+ R m* C) (U tm* B m+ R m* D) (L tm* C) (L tm* D)
\end{code}
%endif
Using these, we can define triangle--triangle multiplication: 
\begin{code}
_t*_ : {s : Splitting} → Tri s → Tri s → Tri s
one t* one = one
two U R L t* two U' R' L' = two (U t* U') (U tm* R' m+ R mt* L') (L t* L')
\end{code}

The final part needed to express the transitive closure specification in Agda is a concept of equality among triangles (and for this, we need equality for matrices and vectors, as before). In all cases, we want to lift the \nanring equality to the datatype in question. As before (see section \ref{Algebra-Equality}), equality takes two objects of a datatype to a proposition (a member of |Set|). We begin with equality among |Vec|, where two one element vectors are equal if their only elements are equal, and vectors that are made up of two parts are equal if both parts are equal (as vectors):
\begin{code}
_v≈_ : {s : Splitting} → Vec s → Vec s → Set
one x v≈ one x' = x R≈ x'
two u v v≈ two u' v' = (u v≈ u') ∧ (v v≈ v')
\end{code}
Note that this (and the remaining equality definitions only apply to \todo{THOMAS: have I not written this already somewhere} vectors with the same splitting) so vectors which contain the same elements can be unequal.

We move on to equality for |Mat|:
\begin{code}
_m≈_ : {s₁ s₂ : Splitting} → Mat s₁ s₂ → Mat s₁ s₂ → Set
Valiant.MatAndTri.sing x m≈ Valiant.MatAndTri.sing x' = x R≈ x'
Valiant.MatAndTri.rVec v m≈ Valiant.MatAndTri.rVec v' = v v≈ v'
Valiant.MatAndTri.cVec v m≈ Valiant.MatAndTri.cVec v' = v v≈ v'
Valiant.MatAndTri.quad A B C D m≈ Valiant.MatAndTri.quad A' B' C' D' = A m≈ A' ∧ B m≈ B' ∧ C m≈ C' ∧ D m≈ D'
\end{code}
And to finish this section, equality for |Tri|:
\begin{code}
_t≈_ : {s : Splitting} → Tri s → Tri s → Set
Valiant.MatAndTri.one t≈ Valiant.MatAndTri.one = ⊤
Valiant.MatAndTri.two U R L t≈ Valiant.MatAndTri.two U' R' L' = U t≈ U' ∧ R m≈ R' ∧ L t≈ L'
\end{code}\todo{THOMAS: Make the actual code have these defs for equality (as opposed to the |data| definitions it now uses}
\todo{THOMAS: Fix references}
\label{Algebra-Equality}
