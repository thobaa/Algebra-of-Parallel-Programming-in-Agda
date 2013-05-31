%if False
\begin{code}
open import Algebra.NANRing
open import Valiant.Splitting
open import Data.Nat
open import Data.Unit
open import Data.Product
module Valiant.Specification (NaSr : NonassociativeSemiring) where
import Valiant.MatAndTri
open Valiant.MatAndTri NaSr
import Valiant.Operations
open Valiant.Operations NaSr
import Valiant.NANRings
open Valiant.NANRings NaSr
open import Algebra.Monoid
--open Algebra.Monoid --NaSr
--open NonassociativeSemiring NaSr renaming (_+_ to _R+_; _*_ to _R*_; _≈_ to _R≈_)
\end{code}
%endif
\subsection{Implementing the algorithm}
Using the above operations, we can now define Valiant's algorithm in Agda, following the outline in Section \ref{Valiant-summing-up}. First we define functions for the overlap part (we introduce two new functions |overlapRow| and |overlapCol| for the cases when one dimension of the matrix is $1$):
\begin{code}
overlapRow : {s : Splitting} → Vec s → Tri s → Vec s
overlapRow (one x)    zer             = one x
overlapRow (two u v)  (tri U⁺ Rˣ L⁺)  = two uˣ vˣ
  where  uˣ  = overlapRow u                 U⁺
         vˣ  = overlapRow (uˣ vm* Rˣ v+ v)  L⁺

overlapCol : {s : Splitting} → Tri s → Vec s → Vec s
overlapCol zer            (one x)    = one x
overlapCol (tri U⁺ Rˣ L⁺) (two u v)  = two uˣ vˣ
  where  vˣ  = overlapCol L⁺  v
         uˣ  = overlapCol U⁺  (Rˣ mv* vˣ v+ u)

overlap : {s₁ s₂ : Splitting} → Tri s₁ → Mat s₁ s₂ → Tri s₂ → Mat s₁ s₂
overlap zer           (sing x)        zer                = sing x
overlap zer           (rVec v)        L⁺                 = rVec (overlapRow v L⁺)
overlap U⁺            (cVec v)        zer                = cVec (overlapCol U⁺ v)
overlap (tri U⁺ Rˣ L⁺)  (quad A B C D)  (tri U'⁺ R'ˣ L'⁺)  = quad  Aˣ Bˣ 
                                                                   Cˣ Dˣ
  where  Cˣ = overlap L⁺  C                             U'⁺
         Aˣ = overlap U⁺  (A m+ Rˣ m* Cˣ)               U'⁺        
         Dˣ = overlap L⁺  (D m+ Cˣ m* R'ˣ)              L'⁺
         Bˣ = overlap U⁺  (B m+ Rˣ m* Dˣ m+ Aˣ m* R'ˣ)  L'⁺
\end{code}
we use |where| definitions to avoid having to repeat code and to show that things are not mutually recursive. Then we define the actual algorithm
\begin{code}
valiant : {s : Splitting} → Tri s → Tri s
valiant zer          = zer
valiant (tri U R L)  = tri U⁺ (overlap U⁺ R L⁺) L⁺
  where  U⁺  = valiant U
         L⁺  = valiant L        
\end{code}
In the next section, we give a specification for the algorithm, and in Section \ref{Proof}, we prove it correct.
\subsection{Specification in Agda}
We are now ready to express the transitive closure problem in Agda. It is a relation between two |Tri|s, that is, a function that takes two |Tri|s, |C⁺| and |C|, and returns the propostion that |C⁺| is the transitive closure of |C|, which is true if |C⁺| and |C| satisfy the specification \eqref{TC} as implemented in Agda:
\begin{code}
_is-tc-of_ : {s : Splitting} → Tri s → Tri s → Set
C⁺ is-tc-of C = C⁺ t≈ C⁺ t* C⁺ t+ C
\end{code}
Additionally, for use in our proof, we want to define three sub-specifications: \eqref{Equation:R-Specification} and its restriction to the case when one dimension is $1$, where the first one is considered as a relation between a |Mat| and a |Tri| (the |Mat| satisfies the specification when inserting the parts of the |Tri|):
\begin{code}
_is-tcMat-of_ : {s₁ s₂ : Splitting} → Mat s₁ s₂ → Tri (bin s₁ s₂) → Set
Rˣ is-tcMat-of (tri U⁺ R L⁺) = Rˣ m≈ U⁺ tm* Rˣ m+ Rˣ mt* L⁺ m+ R
\end{code}
For the row and column part, instead consider a relation between a |Vec| and a pair of a |Vec| and a |Tri|, with the intent that the |Vec| is put on top of the |Tri|. We do this to avoid dealing separately with the $1 \times 1$-vector case: 
\begin{code}
_is-tcRow-of_ : {s : Splitting} → Vec s → Vec s × Tri s → Set
vˣ is-tcRow-of (v , L⁺) = vˣ v≈ vˣ vt* L⁺ v+ v
\end{code}
\begin{code}
_is-tcCol-of_ : {s : Splitting} → Vec s → (Tri s × Vec s) → Set
vˣ is-tcCol-of (U⁺ , v) = vˣ v≈ U⁺ tv* vˣ v+ v
\end{code}


\subsection{The proof}
\label{Valiant:Proof}
\label{Proof}
In this section, we are going to prove the correctness of Valiant's algorithm, as defined in the previous section, in words, for every splitting |s| and every upper triangular matrix |C : Tri s|, |valiant C| is the transitive closure of |C|. We begin by giving the types of the different propositions, so we can use them in an arbitrary order later. The first is the main proposition:
\begin{code}
v-tc    : {s : Splitting}  (C : Tri s) → (valiant C) is-tc-of C
v-mat   : {s₁ s₂ : Splitting} (U⁺ : Tri s₁) (R : Mat s₁ s₂) (L⁺ : Tri s₂) → 
  (overlap U⁺ R L⁺) is-tcMat-of (tri U⁺ R L⁺)
v-row   : {s : Splitting}  (v : Vec s)   (L⁺ : Tri s)   → 
  (overlapRow  v   L⁺)  is-tcRow-of  (v   ,   L⁺)
v-col   : {s : Splitting}  (U⁺ : Tri s)  (v : Vec s)    → 
  (overlapCol  U⁺  v)   is-tcCol-of  (U⁺  ,   v)
\end{code}
giving an object of the first type is easy:
\begin{code}
v-tc zer = tt
v-tc (tri U R L) = v-tc U , v-mat (valiant U) R (valiant L) , v-tc L
\end{code}
The other parts take a bit more code, but that code is for shuffling nonassociative semiring objects around and is easy to write. We include the proof of the correctness of |overlapRow| here:
\begin{code}
v-row (one x) zer = R-sym (proj₁ R+-identity x)
v-row {bin s₁ s₂} (two u v) (tri U R L) = (v-row u U) , (begin 
  overlapRow (overlapRow u U vm* R v+ v) L 
    ≈⟨ v-row (overlapRow u U vm* R v+ v) L ⟩ 
  v₁ v+ (v₂ v+ v) 
    ≈⟨ sym (assoc v₁ v₂ v₃) ⟩
  (v₁ v+ v₂) v+ v
    ≈⟨ ∙-cong (comm v₁ v₂) refl ⟩
  (v₂ v+ v₁) v+ v
    ≈⟨ refl ⟩
  overlapRow u U vm* R v+  overlapRow  
    (overlapRow u U vm* R v+ v) L  vt* L v+ v ∎)
  where  open CM-Reasoning (Vec-commutativeMonoid {s₂})
         v₁ = overlapRow (overlapRow u U vm* R v+ v) L vt* L
         v₂ = overlapRow u U vm* R        
\end{code}
the other proofs are similar.
%if False
\begin{code}
v-mat  zer (sing x) zer = begin 
  x 
    ≈⟨ R-sym (proj₁ R+-identity x) ⟩
  R0 R+ x
    ≈⟨ R+-cong (R-sym (proj₁ R+-identity (R0))) R-refl ⟩
  (R0 R+ R0) R+ x ∎
  where open CM-Reasoning R+-commutativeMonoid
v-mat {one} {bin s₁ s₂} zer (rVec (two u v)) (tri U R L) = lemma₁ , lemma₂
  where lemma₁ = begin 
               overlapRow u U 
                 ≈⟨ v-row u U ⟩ 
               overlapRow u U vt* U v+ u
                 ≈⟨ ∙-cong {(overlapRow u U vt* U)} {zeroVec v+ overlapRow u U vt* U} {u} {u} (sym {zeroVec v+ overlapRow u U vt* U} {overlapRow u U vt* U} (proj₁ identity (overlapRow u U vt* U))) (refl {u}) ⟩
               (zeroVec v+ overlapRow u U vt* U) v+ u ∎
          where open CM-Reasoning (Vec-commutativeMonoid {s₁})
        lemma₂ = begin 
          overlapRow (overlapRow u U vm* R v+ v) L 
            ≈⟨ v-row (overlapRow u U vm* R v+ v) L ⟩ 
          overlapRow (overlapRow u U vm* R v+ v) L vt* L v+ (overlapRow u U vm* R v+ v)
            ≈⟨ {!!} ⟩
          zeroVec v+ (overlapRow u U vm* R v+ overlapRow (overlapRow u U vm* R v+ v) L vt* L) v+ v ∎
          where open CM-Reasoning (Vec-commutativeMonoid {s₂})
v-mat (tri U R L) (cVec (two u v)) zer = {!!} , {!!}
v-mat (tri U R L) (quad A B C D) (tri U' R' L') = {!v-mat!} , {!!} , {!!} , {!!}


v-col U v = {!!}
\end{code}

\begin{spec}
v-row (one x) zer = R-sym (proj₁ R+-identity x)
v-row {bin s₁ s₂} (two u v) (tri U R L) = (v-row u U) , (begin 
  overlapRow (overlapRow u U vm* R v+ v) L 
    ≈⟨ v-row (overlapRow u U vm* R v+ v) L ⟩ 
  overlapRow (overlapRow u U vm* R v+ v) L vt* L v+ 
  (overlapRow u U vm* R v+ v)
    ≈⟨ refl {v₁ v+ (v₂ v+ v₃)} ⟩
  v₁ v+ (v₂ v+ v₃) 
    ≈⟨ sym {(v₁ v+ v₂) v+ v₃} (assoc v₁ v₂ v₃) ⟩
  (v₁ v+ v₂) v+ v₃
    ≈⟨ ∙-cong {v₁ v+ v₂} {_} {v₃} (comm v₁ v₂) (refl {v₃}) ⟩
  (v₂ v+ v₁) v+ v₃
    ≈⟨ refl {v₂ v+ v₁ v+ v₃} ⟩
  overlapRow u U vm* R v+  overlapRow  
    (overlapRow u U vm* R v+ v) L  vt* L v+ v ∎)
  where  open CM-Reasoning (Vec-commutativeMonoid {s₂})
         v₁ = overlapRow (overlapRow u U vm* R v+ v) L vt* L
         v₂ = overlapRow u U vm* R
         v₃ = v
        
\end{spec}
%endif
