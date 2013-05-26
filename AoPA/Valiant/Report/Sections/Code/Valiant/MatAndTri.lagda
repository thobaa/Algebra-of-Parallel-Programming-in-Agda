%if False
\begin{code}
open import Algebra.NANRing
open import Valiant.Splitting
open import Data.Nat
module Valiant.MatAndTri (NaSr : NonassociativeSemiring) where
open NonassociativeSemiring NaSr public renaming (_+_ to _R+_; _*_ to _R*_; _≈_ to _R≈_; +-identity to R+-identity; +-commutativeMonoid to R+-commutativeMonoid; +-cong to R+-cong; sym to R-sym; refl to R-refl)
\end{code}
%endif
Mimicking the above, but using |Splitting|s as indices (the code is essentially the same, with every instance of ``|ℕ|'' replaced by ``|Splitting|''), we first define |Vec| as:
\begin{code}
data Vec : Splitting → Set where
  one  : R → Vec one
  two  : {s₁ s₂ : Splitting} → Vec s₁ → Vec s₂ → Vec (bin s₁ s₂)
\end{code}
We can note that where |Splitting| is a binary tree of elements of the unit type, |Vec| is instead a binary tree of |Carrier| (with elements in the leaves). We move on to defining |Mat| as:
\begin{code}
data Mat : Splitting → Splitting → Set where
  sing : (x : R) → Mat one one
  rVec : {s₁ s₂ : Splitting} → Vec (bin s₁ s₂) → Mat one (bin s₁ s₂)
  cVec : {s₁ s₂ : Splitting} → Vec (bin s₁ s₂) → Mat (bin s₁ s₂) one
  quad : {r₁ r₂ c₁ c₂ : Splitting} →  Mat r₁ c₁ → Mat r₁ c₂ → 
                                      Mat r₂ c₁ → Mat r₂ c₂ → 
                                      Mat (bin r₁ r₂) (bin c₁ c₂)
\end{code}
\label{Tri}
Finally, |Tri|:
\begin{code}
data Tri : Splitting → Set where
  zer   : Tri one
  tri   : {s₁ s₂ : Splitting} → Tri s₁  →  Mat s₁ s₂ → 
                                           Tri s₂ 
                                        → Tri (bin s₁ s₂)
\end{code}
%Here, we note that if we had chosen the approach with empty matrices (see \ref{Section:Empty-Matrices} \todo{THOMAS: check if there should be a reference back here}), and correspondingly, empty |Splitting|s, we might have needed an extra constructor for triangles also \todo{THOMAS: think, is this true???}.

Later, we are going to prove that |Tri s| is a nonassociative semiring for any |s|, and that |Vec s| and |Mat s₁ s₂| are commutative monoids (under addition). For this, we need to define their zero elements (also, we need these to define multiplication, since multiplying a |Tri one| by a |Mat one n| gives a zero matrix): % a zero |Vec|, a zero |Mat| and a zero |Tri|. Even if we decided against doing this, we would need to define the zero elements somewhere, since we need multiplication to define our specification of the transitive closure, and multiplying a |Tri one| by a |Mat one s| should result in a |Mat one s| that is zero everywhere. 

We define them by pattern matching on splittings:
\begin{code}
zeroVec : {s : Splitting} → Vec s
zeroVec {one}        = one R0
zeroVec {bin s₁ s₂}  = two zeroVec zeroVec

zeroMat : {s₁ s₂ : Splitting} → Mat s₁ s₂
zeroMat {one}        {one}          = sing R0
zeroMat {one}        {bin s₁ s₂}    = rVec zeroVec
zeroMat {bin s₁ s₂}  {one}          = cVec zeroVec
zeroMat {bin s₁ s₂}  {bin s₁' s₂'}  = quad  zeroMat zeroMat 
                                            zeroMat zeroMat

zeroTri : {s : Splitting} → Tri s
zeroTri {one}        = zer
zeroTri {bin s₁ s₂}  = tri zeroTri zeroMat zeroTri
\end{code}
