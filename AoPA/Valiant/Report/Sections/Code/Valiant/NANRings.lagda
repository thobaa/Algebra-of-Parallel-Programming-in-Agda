%if False
\begin{code}
open import Algebra.NANRing
open import Valiant.Splitting
open import Data.Unit
open import Data.Product using (proj₁; _,_)
--open import Algebra.Structures --using (CommutativeMonoid)
--open import Algebra hiding (Monoid)

open import Algebra.NANRing
--open import Algebra.Reasoning
open import Algebra.Monoid

module Valiant.NANRings (NaSr : NonassociativeSemiring) where
import Valiant.MatAndTri
open Valiant.MatAndTri NaSr
import Valiant.Operations
open Valiant.Operations NaSr
--open NonassociativeSemiring NaSr renaming (_+_ to _R+_; _*_ to _R*_; +-identity to R+-identity; _≈_ to _R≈_; Carrier to R)
\end{code}
%endif
\subsection{Nonassociative Semirings}
We will now prove that |Vec|, |Mat| and |Tri| are commutative monoids with |_v+_|, |_m+_| and |_t+_|, and |Tri| is a nonassociative semiring with |_t+_| and |_t*_| as defined above. One big reason for doing this is that it will make it possible to use the equational reasoning introduced in Section \ref{Section-where-eqr-helper-is-defined}. We will prove
\begin{spec}
∀ {s}      →   IsCommutativeMonoid  _v≈_  _v+_  (zeroVec {s})
∀ {s₁ s₂}  →   IsCommutativeMonoid  _m≈_  _m+_  (zeroMat {s₁} {s₂})
∀ {s}      →   IsCommutativeMonoid  _t≈_  _t+_  (zeroTri {s})
∀ {s}      →   IsNonassociativeSemiring  _t≈_ _t+_ _t*_ (zeroTri {s})
\end{spec}
%if False
\begin{code}
Vec-isCommutativeMonoid : {s : Splitting}      →  IsCommutativeMonoid _v≈_ _v+_ (zeroVec {s})
Mat-isCommutativeMonoid : {s₁ s₂ : Splitting} → IsCommutativeMonoid _m≈_ _m+_ (zeroMat {s₁} {s₂})
Tri-isCommutativeMonoid : {s : Splitting} → IsCommutativeMonoid _t≈_ _t+_ (zeroTri {s})
Tri-isNonassociativeSemiring : {s : Splitting} → IsNonassociativeSemiring _t≈_ _t+_ _t*_ (zeroTri {s})
\end{code}
%endif
The reason we include the Splitting in the zero elements is that we need to make Agda infer what datatype we are talking about. To prove these things is generally very easy, but requires a lot of code. Complete proofs are available in our library. 
We also define instances of |CommutativeMonoid| (for |Vec|, |Mat| and |Tri|) and |NonassociativeSemiring| (for |Tri|).

Proving things about addition means pushing the statements into the algebraic structure below. We exemplify by proving that |zeroVec| is the left identity of |_v+_|:
\begin{code}
Vec-identityˡ : {s : Splitting} → (x : Vec s) → zeroVec v+ x v≈ x
Vec-identityˡ (one x)    = proj₁ R+-identity x
Vec-identityˡ (two u v)  = (Vec-identityˡ u) , (Vec-identityˡ v)
\end{code}
%if False
\begin{code}
postulate 
  cheat1 : {s : Splitting} → IsCommutativeMonoid _v≈_ _v+_ (zeroVec {s})
  cheat2 : {s₁ s₂ : Splitting} → IsCommutativeMonoid _m≈_ _m+_ (zeroMat {s₁} {s₂})
  cheat3 : {s : Splitting} → IsNonassociativeSemiring _t≈_ _t+_ _t*_ (zeroTri {s})
  cheat4 : {s : Splitting} → IsCommutativeMonoid _t≈_ _t+_ (zeroTri {s})
Vec-isCommutativeMonoid = cheat1 
Mat-isCommutativeMonoid = cheat2
Tri-isCommutativeMonoid = cheat4
Tri-isNonassociativeSemiring = cheat3
\end{code}
%endif
%if False
\begin{code}
Vec-commutativeMonoid : {s : Splitting} → CommutativeMonoid
Vec-commutativeMonoid {s} = record { isCommutativeMonoid = Vec-isCommutativeMonoid {s} }
Mat-commutativeMonoid : {s₁ s₂ : Splitting} →  CommutativeMonoid
Mat-commutativeMonoid {s₁} {s₂} = record { isCommutativeMonoid = Mat-isCommutativeMonoid {s₁} {s₂}}
Tri-commutativeMonoid : {s : Splitting} →  CommutativeMonoid
Tri-commutativeMonoid {s} = record { isCommutativeMonoid = Tri-isCommutativeMonoid {s} }
Tri-nonassociativeSemiring : {s : Splitting} → NonassociativeSemiring
Tri-nonassociativeSemiring {s} = record { isNonassociativeSemiring = Tri-isNonassociativeSemiring {s} }
\end{code}
%endif

Proving things about multiplication also means moving the properties down to the nonassociative semiring below, but here, the path is longer. We examplify the beginning of this path by giving the proof that |zeroTri| is a left zero of |_t*_|, and that |_t*_| distributes over |_t+_|, on the left:
%if False
\begin{code}
postulate 
  tm*-zeroˡ : {s₁ s₂ : Splitting} → (x : Mat s₁ s₂) → zeroTri tm* x m≈ zeroMat
  mt*-zeroˡ : {s₁ s₂ : Splitting} → (x : Tri s₂) → (zeroMat {s₁} {s₂}) mt* x m≈ zeroMat
\end{code}
%endif
\begin{code}
t*-zeroˡ : {s : Splitting} → (x : Tri s) → zeroTri t* x t≈ zeroTri
t*-zeroˡ              zer          = tt
t*-zeroˡ {bin s₁ s₂}  (tri U R L)  = 
  (  t*-zeroˡ U                                  
  ,  e'∙e''≈e  Mat-commutativeMonoid {zeroTri tm* R} {zeroMat mt* L} 
               (tm*-zeroˡ R) (mt*-zeroˡ {s₁} L)  
  ,  t*-zeroˡ L 
  )
\end{code}
where |tt| is the constructor of the true proposition (we want to prove that any two |zer| are equal), and
\begin{spec}
tm*-zeroˡ  : {s₁ s₂ : Splitting} → (x : Mat s₁ s₂) 
           → zeroTri tm* x m≈ zeroMat
mt*-zeroˡ  : {s₁ s₂ : Splitting} → (x : Tri s₂) 
           → (zeroMat {s₁} {s₂}) mt* x m≈ zeroMat
\end{spec}
are the proofs (that we would need to write) that |zeroTri| is a ``left zero'' of |_tm*_|, and that |zeroMat| is a ``left zero'' of |_mt*_| (if the concept of a zero is slightly generalized to ``operations'' |f : A → B → A| and |f : A → B → B|).
