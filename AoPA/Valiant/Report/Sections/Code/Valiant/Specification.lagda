%if False
\begin{code}
open import Algebra.NANRing
open import Valiant.Splitting
open import Data.Nat
open import Data.Unit
open import Data.Product
module Valiant.Specification (NANR : NonAssociativeNonRing) where
import Valiant.MatAndTri
open Valiant.MatAndTri NANR
import Valiant.Operations
open Valiant.Operations NANR
open NonAssociativeNonRing NANR renaming (_+_ to _R+_; _*_ to _R*_; 0# to R0; _≈_ to _R≈_; refl to R-refl)
\end{code}
%endif
\subsubsection{Specification and Proof in Agda}\todo{ALL: the specification part is very small -- either move up to previous, or keep with proof here.}
With the above operations, and the fact that they form \nanring s, we are now ready to express the transitive closure problem in Agda. It is a relation between two |Tri|s, that is, a function that takes two |Tri|s, |C⁺| and |C|, and returns the propostion that |C⁺| is the transitive closure of |C|, which is true if |C⁺| and |C| satisfy the specification \eqref{Equation:JPTSpec}, with multiplication, addition and equality replaced by their triangle versions:
\begin{code}
_is-tc-of_ : {s : Splitting} → Tri s → Tri s → Set
C⁺ is-tc-of C = C⁺ t≈ C⁺ t* C⁺ t+ C
\end{code}
Additionally, for use in our proof, we want to define the various subspecifications we used, from equations \eqref{R-Spec}, \eqref{Col-Spec} and \eqref{Row-Spec}, which are relations between a |Mat| or |Vec| and a |Tri|. Each of these concerns a different kind of |Tri|, and we are able to pattern match to get out the parts used in the abovementioned equations.
\todo{THOMAS: chech out how the spacing differs when using different code blocks} 
\todo{THOMAS: byt ut $R^*$ mot $R^\times$ or something}
\begin{code}
_is-tcMat-of_ : {s₁ s₂ : Splitting} → Mat s₁ s₂ → Tri (bin s₁ s₂) → Set
Rˣ is-tcMat-of (two U⁺ R L⁺) = Rˣ m≈ U⁺ tm* Rˣ m+ Rˣ mt* L⁺ m+ R
\end{code}
\begin{code}
_is-tcRow-of_ : {s : Splitting} → Vec s → Tri (bin one s) → Set
(one x) is-tcRow-of two one (sing x') one = x R≈ x'
vˣ is-tcRow-of two one (rVec v) L⁺ = vˣ v≈ vˣ vt* L⁺ v+ v
--vˣ is-tcRow-of (two one (rVec v) L⁺) = vˣ v≈ vˣ vt* L⁺ v+ v
\end{code}
\begin{code}
_is-tcCol-of_ : {s : Splitting} → Vec s → Tri (bin s one) → Set
one x is-tcCol-of two one (sing x') one = x R≈ x'
vˣ is-tcCol-of (two U⁺ (cVec v) one) = vˣ v≈ U⁺ tv* vˣ v+ v
\end{code}
Where we restrict the types in the |Vec| specifications to vector with length at least $2$, since this is the only case they need to handle.

Now, we begin to define Valiant's algorithm in Agda, and in the next section, we prove the proposition |(valiant C) is-tc-of C|. 
We begin by defining the overlap part, and to do this, we define the overlap part for row vectors and column vectors---as separate functions that work on |Vec|s, since their recursive calls only affect vectors:\todo{THOMAS: Clear up reason}\todo{THOMAS: Fix discussion about overlap case in different section, it is wrong!}
\begin{code}
overlapRow : {s : Splitting} → Vec s → Tri s → Vec s
overlapRow (one x) one = one x
overlapRow (two u v) (two U⁺ Rˣ L⁺) = two uˣ vˣ
  where uˣ = overlapRow u U⁺
        vˣ = overlapRow (u vm* Rˣ v+ v) L⁺

overlapCol : {s : Splitting} → Tri s → Vec s → Vec s
overlapCol one (one x) = one x
overlapCol (two U⁺ Rˣ L⁺) (two u v) = two uˣ vˣ
  where vˣ = overlapCol L⁺ v
        uˣ = overlapCol U⁺ (Rˣ mv* vˣ v+ u)
\end{code}
Then we define the function the function that calculates the overlap part for arbitrary |Mat|s, as defined in Section \ref{Overlap-section}. It should take as input a |Tri|, a |Mat|, and a |Tri|, and return a |Mat|, that should satisfy |(overlap U R L) is-tcMat-of (two U R L)|:\todo{THOMAS: expand overlap step in algorithm (in other section), so it summarizes things}
\begin{code}
overlap : {s₁ s₂ : Splitting} → Tri s₁ → Mat s₁ s₂ → Tri s₂ → Mat s₁ s₂
overlap one (sing x) one = sing x
overlap one (rVec v) L⁺ = rVec (overlapRow v L⁺)
overlap U⁺ (cVec v) one = cVec (overlapCol U⁺ v)
overlap (two U⁺ Rˣ L⁺) (quad A B C D) (two U'⁺ R'ˣ L'⁺) = quad Aˣ Bˣ Cˣ Dˣ
  where Cˣ = overlap L⁺ C U'⁺
        Aˣ = overlap U⁺ (A m+ Rˣ m* Cˣ) U'⁺        
        Dˣ = overlap L⁺ (D m+ Cˣ m* R'ˣ) L'⁺
        Bˣ = overlap U⁺ (B m+ Rˣ m* Dˣ m+ Aˣ m* R'ˣ) L'⁺
\end{code}
Where we have used |where| blocks to avoid repeating computations (and avoid repeating the code for them).

Finally, we define Valiant's algorithm:
\begin{code}
valiant : {s : Splitting} → Tri s → Tri s
valiant Valiant.MatAndTri.one = one
valiant (Valiant.MatAndTri.two U R L) = two U⁺ (overlap U⁺ R L⁺) L⁺
  where U⁺ = (valiant U)
        L⁺ = (valiant L)        
\end{code}
we note that the algorithm is fairly straightforward, since some of the complexity of it is hidden in the definitions of matrix multiplication. Now, we are ready to prove the correctness.
\subsubsection{Proof}
In this section, we are going to prove the correctness of Valiant's algorithm, as defined in the previous section, that is, we will prove that it satisfies the specification we gave above, or, in words, for every splitting |s| and every upper triangular matrix |C : Tri s|, |valiant C| is the transitive closure of |C|. We begin by giving the proofs of the different propositions, so we can use them in an arbitrary order later. The first is the main proposition:
\begin{code}
valiant-correctness : {s : Splitting} (C : Tri s) → (valiant C) is-tc-of C
valiant-mat-correctness : {s₁ s₂ : Splitting} (U⁺ : Tri s₁) (R : Mat s₁ s₂) (L⁺ : Tri s₂) → overlap U⁺ R L⁺ is-tcMat-of two U⁺ R L⁺

rvec : {s : Splitting} → Vec s → Mat one s
rvec {one} (Valiant.MatAndTri.one x) = Valiant.MatAndTri.sing x
rvec {bin s₁ s₂} v = Valiant.MatAndTri.rVec v
cvec : {s : Splitting} → Vec s → Mat s one
cvec {one} (Valiant.MatAndTri.one x) = Valiant.MatAndTri.sing x
cvec {bin s₁ s₂} v = Valiant.MatAndTri.cVec v
valiant-row-correctness : {s : Splitting} (v : Vec s) (L⁺ : Tri s) → overlapRow v L⁺ is-tcRow-of two one (rvec v) L⁺
--{s₁ s₂ : Splitting} (v : Vec (bin s₁ s₂)) (L⁺ : Tri (bin s₁ s₂)) → overlapRow v L⁺ is-tcRow-of two one (rVec v) L⁺

--valiant-row-correctness' : {s : Splitting} (v : Vec s) (L⁺ : Tri s) → overlapRow v L⁺ is-tcRow-of two one {!rvec v!} L⁺

--valiant-row-correctness' = {!!}
valiant-col-correctness : {s : Splitting} (U⁺ : Tri s) (v : Vec s) → overlapCol U⁺ v is-tcCol-of two U⁺ (cvec v) one
\end{code}

\begin{code}
valiant-correctness one = tt
valiant-correctness (two U R L) = valiant-correctness U , valiant-mat-correctness (valiant U) R (valiant L) , valiant-correctness L
valiant-mat-correctness Valiant.MatAndTri.one (Valiant.MatAndTri.sing x) Valiant.MatAndTri.one = {!!}
valiant-mat-correctness one (rVec v) L = {!valiant-row-correctness v L!}
--  where open EqR
valiant-mat-correctness (Valiant.MatAndTri.two U R L) (Valiant.MatAndTri.cVec v) Valiant.MatAndTri.one = {!!}
valiant-mat-correctness U (Valiant.MatAndTri.quad A B C D) L = {!!}

valiant-row-correctness (Valiant.MatAndTri.one x) Valiant.MatAndTri.one = R-refl
valiant-row-correctness (Valiant.MatAndTri.two u v) (Valiant.MatAndTri.two U R L) = ({!valiant-row-correctness u U!}) , {!valiant-row-correctness (u vm* R v+ v) L!}
valiant-col-correctness U v = {!!}
\end{code}
