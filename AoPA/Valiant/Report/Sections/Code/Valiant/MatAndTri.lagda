%if False
\begin{code}
open import Algebra.NANRing
open import Valiant.Splitting
open import Data.Nat
module Valiant.MatAndTri (NASR : NonAssociativeNonRing) where
open NonAssociativeNonRing NASR public renaming (_+_ to _R+_; _*_ to _R*_; _≈_ to _R≈_; +-identity to R+-identity)
\end{code}
%endif
Mimicking the above, but using |Splitting|s as indices (the code is essentially the same, with every instance of ``|ℕ|'' replaced by ``|Splitting|''), we first define |Vec| as:
\begin{code}
data Vec : Splitting → Set where
  one : (x : R) → Vec one
  two : {s₁ s₂ : Splitting} → Vec s₁ → Vec s₂ → Vec (bin s₁ s₂)
\end{code}
We can note that where |Splitting| is a binary tree of elements of the unit type, |Vec| is instead a binary tree of |Carrier| (with elements in the leaves). We move on to defining |Mat| as:
\begin{code}
data Mat : Splitting → Splitting → Set where
  sing : (x : R) → Mat one one
  rVec : {s₁ s₂ : Splitting} → (v : Vec (bin s₁ s₂)) → Mat one (bin s₁ s₂)
  cVec : {s₁ s₂ : Splitting} → (v : Vec (bin s₁ s₂)) → Mat (bin s₁ s₂) one
  quad : {r₁ r₂ c₁ c₂ : Splitting} →  Mat r₁ c₁ → Mat r₁ c₂ → 
                                      Mat r₂ c₁ → Mat r₂ c₂ → 
                                      Mat (bin r₁ r₂) (bin c₁ c₂)
\end{code}
\todo{THOMAS: Check for number of constructors in JP's |Tri| definition}
The definition of the last datatype involved, |Tri| is straightforward from the subdivision made above in Section \ref{Section:Subdivision-in-Specification}. There is only one base case, that of the $1 \times 1$ zero triangle (equal to the $1 \times 1$ zero matrix when viewed as an upper triangular marix), and putting together |Tri|s is straightforward since the upper triangular matrices need to be square, now that our matrices can have any shape, and the definition guarantees that the two step splitting in Section \ref{Section:Two-Step-Splitting} can be done:
\begin{code}
data Tri : Splitting → Set where
  one : Tri one
  two : {s₁ s₂ : Splitting} → (U : Tri s₁) → (R : Mat s₁ s₂) → (L : Tri s₂) → Tri (bin s₁ s₂)
\end{code}
Where again, the ordering of the arguments to |two| (it takes \emph{two} |Tri|s) is such that if we introduce a line break after |Mat s₁ s₂|, and indent |Tri s₂| so it is below |Mat s₁ s₂|, they have the shape of an upper triangular matrix.

Here, we note that if we had chosen the approach with empty matrices (see \ref{Section:Empty-Matrices} \todo{THOMAS: check if there should be a reference back here}), and correspondingly, empty |Splitting|s, we might have needed an extra constructor for triangles also \todo{THOMAS: think, is this true???}.

Later, we are going to prove that |Tri s| is a \nanring for any |s|, and that |Vec s| and |Mat s₁ s₂| are commutative monoids (under addition). For this, we need to define their zero elements, that is a zero |Vec|, a zero |Mat| and a zero |Tri|. Even if we decided against doing this, we would need to define the zero elements somewhere, since we need multiplication to define our specification of the transitive closure, and multiplying a |Tri one| by a |Mat one s| should result in a |Mat one s| that is zero everywhere. 

We define them by pattern matching on the implicit splittings:
\begin{code}
zeroVec : {s : Splitting} → Vec s
zeroVec {one} = one R0
zeroVec {bin s₁ s₂} = two zeroVec zeroVec

zeroMat : {s₁ s₂ : Splitting} → Mat s₁ s₂
zeroMat {one} {one} = sing R0
zeroMat {one} {bin s₁ s₂} = rVec zeroVec
zeroMat {bin s₁ s₂} {one} = cVec zeroVec
zeroMat {bin s₁ s₂} {bin s₁' s₂'} = quad zeroMat zeroMat zeroMat zeroMat

zeroTri : {s : Splitting} → Tri s
zeroTri {one} = one
zeroTri {bin s₁ s₂} = two zeroTri zeroMat zeroTri
\end{code}
