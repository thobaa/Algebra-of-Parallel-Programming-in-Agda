%if False
\begin{code}
open import Algebra.NANRing
open import Valiant.Splitting
open import Data.Nat using ()
open import Data.Unit
open import Data.Product
--open import Algebra.Structures --using (CommutativeMonoid)
--open import Algebra hiding (Monoid)

open import Algebra.NANRing
open import Algebra.Reasoning
open import Algebra.Monoid

module Valiant.NANRings (NANR : NonAssociativeNonRing) where
import Valiant.MatAndTri
open Valiant.MatAndTri NANR
import Valiant.Operations
open Valiant.Operations NANR
open NonAssociativeNonRing NANR renaming (_+_ to _R+_; _*_ to _R*_; 0# to R0; +-identity to R+-identity; _≈_ to _R≈_; Carrier to R)
\end{code}
%endif
\subsubsection{Proof that they are NANRings}
We will now prove that |Vec|, |Mat| and |Tri| are commutative monoids with |_v+_|, |_m+_| and |_t+_|, and |Tri| is a \nanring with |_t+_| and |_t*_| as defined above. One big reason for doing this is that it will make it possible, and easier, to reason about equations containing elements from the different datatypes. We can use something similar to the equational reasoning used in Section \ref{Section-with-EqR}, with the added help of the axioms of a commutative monoid or a \nanring. That is, we will prove 
\begin{code}
Vec-isCommutativeMonoid : {s : Splitting} → IsCommutativeMonoid _v≈_ _v+_ (zeroVec {s})
Mat-isCommutativeMonoid : {s₁ s₂ : Splitting} → IsCommutativeMonoid _m≈_ _m+_ (zeroMat {s₁} {s₂})
Tri-isCommutativeMonoid : {s : Splitting} → IsCommutativeMonoid _t≈_ _t+_ (zeroTri {s})
Tri-isNonAssociativeNonRing : {s : Splitting} → IsNonAssociativeNonRing _t≈_ _t+_ _t*_ (zeroTri {s})
\end{code}
the reason we include the Splitting in the zero element is that we need to make Agda infer what datatype we are talking about. To prove these things is generally very easy, but requires a lot of code. The interested reader is referred to the full code at \cite{CODE}. 

The approach for proving things about addition involves lifting statements into the ground \nanring. We examplify by proving the |identityˡ|-lemma for |Vec|, that is, that |zeroVec| is the left identity of |_v+_|:
\begin{code}
Vec-identityˡ : {s : Splitting} → (x : Vec s) → zeroVec v+ x v≈ x
Vec-identityˡ (one x) = proj₁ R+-identity x
Vec-identityˡ (two u v) = (Vec-identityˡ u) , (Vec-identityˡ v)
\end{code}
%if False
\begin{code}
postulate 
  cheat1 : {s : Splitting} → IsCommutativeMonoid _v≈_ _v+_ (zeroVec {s})
  cheat2 : {s₁ s₂ : Splitting} → IsCommutativeMonoid _m≈_ _m+_ (zeroMat {s₁} {s₂})
  cheat3 : {s : Splitting} → IsNonAssociativeNonRing _t≈_ _t+_ _t*_ (zeroTri {s})
  cheat4 : {s : Splitting} → IsCommutativeMonoid _t≈_ _t+_ (zeroTri {s})
Vec-isCommutativeMonoid = cheat1 
Mat-isCommutativeMonoid = cheat2
Tri-isCommutativeMonoid = cheat4
Tri-isNonAssociativeNonRing = cheat3
\end{code}
%endif
Then, we can define instances of |CommutativeMonoid| and |NonAssociativeNonRing|:
\begin{code}
Vec-CommutativeMonoid : {s : Splitting} → CommutativeMonoid
Vec-CommutativeMonoid {s} = record { isCommutativeMonoid = Vec-isCommutativeMonoid {s} }
Mat-CommutativeMonoid : {s₁ s₂ : Splitting} →  CommutativeMonoid
Mat-CommutativeMonoid {s₁} {s₂} = record { isCommutativeMonoid = Mat-isCommutativeMonoid {s₁} {s₂}}
Tri-CommutativeMonoid : {s : Splitting} →  CommutativeMonoid
Tri-CommutativeMonoid {s} = record { isCommutativeMonoid = Tri-isCommutativeMonoid {s} }
Tri-NonAssociativeNonRing : {s : Splitting} → NonAssociativeNonRing
Tri-NonAssociativeNonRing {s} = record { isNonAssociativeNonRing = Tri-isNonAssociativeNonRing {s} }
\end{code}

To partly motivate proving that they are (and further, using algebraic structures) algebraic structures, we prove two simple lemmas about |CommutativeMonoid|s. The first is used repeatedly when proving that |zeroTri| is an annihilating element:\todo{fix the all a b below}
\begin{code}
0′+0″≈0 : (cm : CommutativeMonoid) → let open CommutativeMonoid cm renaming (_∙_ to _+_) in {0′ 0″ : Carrier} → 0′ ≈ ε → 0″ ≈ ε → 0′ + 0″ ≈ ε
0′+0″≈0 cm = {!!}
  where open CM-Reasoning cm
\end{code}
The second is used very frequently when proving that |_t*_| distributes over |_t+_|:
\begin{code}
rearr : {!!}
rearr = {!!}
\end{code}
Proving things about multiplication also involves moving the properties down to the ground \nanring, but here, the path is longer. We examplify the beginning of this path by giving the proof that |zeroTri| is a left zero of |_t*_|, and that |_t*_| distributes over |_t*_|, on the left:
%if False
\begin{code}
postulate 
  tm*-zeroˡ : {s₁ s₂ : Splitting} → (x : Mat s₁ s₂) → zeroTri tm* x m≈ zeroMat
  mt*-zeroˡ : {s₁ s₂ : Splitting} → (x : Tri s₂) → (zeroMat {s₁} {s₂}) mt* x m≈ zeroMat
\end{code}
%endif
\begin{code}
t*-zeroˡ : {s : Splitting} → (x : Tri s) → zeroTri t* x t≈ zeroTri
t*-zeroˡ one = tt
t*-zeroˡ {bin s₁ s₂} (two U R L) = t*-zeroˡ U , 0′+0″≈0 Mat-CommutativeMonoid  {zeroTri tm* R} {zeroMat mt* L} (tm*-zeroˡ R) (mt*-zeroˡ {s₁} L) , t*-zeroˡ L
\end{code}
where 
\begin{spec}
tm*-zeroˡ : {s₁ s₂ : Splitting} → (x : Mat s₁ s₂) → zeroTri tm* x m≈ zeroMat
mt*-zeroʳ : {s₁ s₂ : Splitting} → (x : Tri s₂) → (zeroMat {s₁} {s₂}) mt* x m≈ zeroMat
\end{spec}
are the proofs that |zeroTri| is a left zero of |_tm*_|, and that |zeroMat| is a leftzero of |_mt*_| (where the concept of a zero is slightly generalized to allow ``operations'' |f : A → B → A| or |f : A → B → B|).
\begin{code}
t*-distribˡ : {s : Splitting} → (x y z : Tri s) → x t* (y t+ z) t≈ x t* y t+ x t* z
t*-distribˡ = {!!}
\end{code}
\todo{THOMAS: Find and prove lemmas (rearrangeLemma)}
