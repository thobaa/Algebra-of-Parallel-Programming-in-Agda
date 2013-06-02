%if False
\begin{code}
open import Data.Nat
open import Data.Nat.Properties
open import Relation.Nullary using (yes; no)
open import Data.Sum renaming (_⊎_ to _∨_)
open import Data.Product using (proj₁; proj₂; _×_)
open import Data.Fin using (Fin; toℕ) renaming (zero to fzero; suc to fsuc)
open import Algebra.NANRing
open import Algebra.Monoid
module Algebra.Triangle (NaSr : NonassociativeSemiring) where

import Algebra.Matrix
open Algebra.Matrix NaSr
import Algebra.MatrixOperations
open Algebra.MatrixOperations NaSr
\end{code}
%endif
\label{Triangle}
\label{Section:Triangle}
In Agda, there are two obvious ways to define a triangular matrix. The first is to use records, where a triangular matrix is a matrix along with a proof that it is triangular. The second way would be to use functions that take two arguments and return a ring element, but where the second argument must be strictly greater than the first. We illustrate these two approaches in Figure \ref{Figure:TriangularMatrixOrTriangle}.
\begin{figure}
  \centering
  %\missingfigure{draw figure of two matrices, one with zeros below diagonal, one with nothing (or stars or somethign)}
  \begin{equation*}
    \begin{pmatrix}
      0      & a_{1 2} & \hdots  & \hdots & a_{1 n}   \\
      0      & 0       & a_{2 3} & \hdots & a_{2 n}   \\
      \vdots & \vdots  & \ddots  & \ddots & \vdots    \\
      0      & \hdots  & \hdots  & 0      & a_{n-1 n} \\
      0      & 0       & 0       & 0      & 0      
    \end{pmatrix}
    \quad 
    \begin{pmatrix}
             & a_{1 2} & \hdots  & \hdots & a_{1 n}   \\
             &         & a_{2 3} & \hdots & a_{2 n}   \\
             &         &         & \ddots & \vdots    \\
             &         &         &        & a_{n-1 n} \\
             &         &         &        &        
    \end{pmatrix}
  \end{equation*}
  \caption{A figure showing an upper triangular matrix on the left and a ``triangle'' on the right. \label{Figure:TriangularMatrixOrTriangle}}
\end{figure}

We choose the first approach here, because it will make it possible to use the majority of the work from when we proved that matrices form a nonassociative semiring to show that triangular matrices also form a nonassociative semiring (or a ring, if their elements come from a ring), under the obvious multiplication, addition and equality. The only problem we will have is to prove that the multiplication is closed. %Here it is important repeat that by triangular, we mean upper triangular (although everything would work equally well if we used it to mean lower triangular, as long as it doesn't include both upper and lower) if both upper and lower triangular matrices were allowed, we would not get a ring, , since it is well known that any matrix can be factorized as a product of a lower and an upper triangular matrix.

One additional reason for not choosing the second approach is that it involves more inequalities between elements of |Fin|, and inequalities for |Fin| are a bit difficult to work with in Agda.

%Thus we define triangular matrices of triangularity |d| (and give them the name |Triangle|):
%if False
\begin{spec}
infix 6 _-_
_-_ : {n : ℕ} → Fin n → Fin n → Fin n
fzero - j = fzero
fsuc i - fzero = fsuc i
fsuc i - fsuc i' = raise (i - i')
  where raise : {n : ℕ} → Fin n → Fin (suc n)
        raise fzero = fzero
        raise (fsuc i0) = fsuc (raise i0)
infix 5 _≤_
data _≤_ : {n : ℕ} → Fin n → Fin n →  Set where
  fz≤i  : {n : ℕ} {i : Fin (suc n)} → fzero ≤ i
  fs≤fs : {n : ℕ} {i j : Fin (suc n)} → i ≤ j → fsuc i ≤ fsuc j
\end{spec}
%endif
We define a datatype of triangular matrices, which we name |Triangle| as a record with a field |mat| for a matrix, and a field |tri| for a proof that it is zero on and below the diagonal:
\begin{code}
record Triangle (n : ℕ) : Set where
  field 
    mat  : Matrix n n
    tri  : (i j : Fin n) → toℕ j ≤ toℕ i → mat i j R≈ R0
\end{code}

We also define two |Triangle|s to be equal if they have the same underlying matrix, since the proof is only there to ensure us that they are actually upper triangular and should not matter when comparing matrices.
\begin{code}
_T≈_ : {n : ℕ} → Triangle n → Triangle n → Set
A T≈ B = Triangle.mat A M≈ Triangle.mat B
\end{code}

Next, we go on to define addition and multiplication of triangles. We apply the matrix operations to the |mat| fields and modify the |tri| proofs appropriately. For addition, the proof modification is straightforward (we take care of the |R0 R+ R0| with |e'∙e''≈e|):
\begin{code}
_T+_ : {n : ℕ} → Triangle n → Triangle n → Triangle n
A T+ B = record 
  {  mat  = Triangle.mat A M+ Triangle.mat B
  ;  tri  = λ i j i≤j → e'∙e''≈e R+-CM  (Triangle.tri A i j i≤j) 
                                        (Triangle.tri B i j i≤j) 
  }
\end{code}

For multiplication, the proof modification required is a bit more complicated, and requires a lemma related to dot-products. We first prove that the dot product of two vectors $u$ and $v$ is zero if for every $i$, either the $i$th component of $u$ or the $i$th component of $v$ is zero. To do this, we need a further (short) lemma that the product of two elements, one of which is zero is zero. We include the case where the first element is zero:
\begin{code}
r*s-zero : (r s : R) → (r R≈ R0) ∨ (s R≈ R0) → r R* s R≈ R0
r*s-zero r s (inj₁ r≈0) = begin 
  r R* s 
    ≈⟨ *-cong r≈0 refl ⟩
  R0 R* s
    ≈⟨ proj₁ R-zero s ⟩
  R0 ∎
  where open CM-Reasoning R+-CM
\end{code}
and the case where |s| is zero is similar.
%if False
\begin{code}
r*s-zero r s (inj₂ s≈0) = begin 
  r R* s 
    ≈⟨ *-cong refl s≈0 ⟩  
  r R* R0 
    ≈⟨ proj₂ R-zero r ⟩ 
  R0 ∎
  where open CM-Reasoning R+-CM
\end{code}
%endif
\begin{code}
u∙v-zero :  ∀ {n} (u v : Vector n)  → 
            ((i : Fin n) → u i R≈ R0 ∨ v i R≈ R0) → u ∙ v R≈ R0
u∙v-zero {zero}   u v one0 = R-refl
u∙v-zero {suc n}  u v one0 = begin 
  (head u R* head v) R+ (tail u ∙ tail v)
    ≈⟨ R+-cong  (r*s-zero (u fzero) (v fzero) (one0 fzero)) 
                (u∙v-zero (tail u) (tail v) (λ i → one0 (fsuc i))) ⟩ 
  R0 R+ R0 
    ≈⟨ proj₁ R+-identity R0 ⟩ 
  R0 ∎
  where open CM-Reasoning R+-CM renaming (_∙_ to _+_)
\end{code}
%if False
\begin{code}

        head : {n : _} → Vector (suc n) → R
        head v = v Data.Fin.zero
        tail : {n : _} → Vector (suc n) → Vector n
        tail v = λ x → v (Data.Fin.suc x)
\end{code}
%endif
Next, we use the fact that inequalities among natural numbers are decidable, see the end of Section \ref{CH}, to extract a proof that for an arbitrary  $k$, if $j \le i$, then either $A_{i k}$ or $B_{k j}$ is zero (if $k \le i$ then $A_{i k}$ is zero, and if $\lnot (k \le i)$ then $j \le k$, so $B_{j k}$ is zero):
\begin{code}
one0-mat : {n : _} → (A B : Triangle n) → (i j : Fin n) 
         → toℕ j ≤ toℕ i → (k : Fin n) 
         → Triangle.mat A i k R≈ R0 ∨ Triangle.mat B k j R≈ R0
one0-mat A B i j j≤i k  with toℕ k ≤? toℕ i 
one0-mat A B i j j≤i k  | yes  k≤i  = inj₁ (Triangle.tri A i k k≤i)
one0-mat A B i j j≤i k  | no   k≰i  = inj₂ (Triangle.tri B k j (begin 
  toℕ j 
    ≤⟨ j≤i ⟩ 
  toℕ i
    ≤⟨ n≤1+n (toℕ i) ⟩
  suc (toℕ i)
    ≤⟨ ≰⇒> k≰i ⟩
  toℕ k ∎))
  where open Data.Nat.≤-Reasoning
\end{code}
where the module |≤-Reasoning| lets us use syntax similar to the one we used in Section \ref{CM-EqReasoning} to prove that inequalities among natural numbers.

Now, we combine these to give the proof of triangularity for |A T* B|.
\begin{code}
_T*_ : {n : ℕ} → Triangle n → Triangle n → Triangle n
A T* B = record 
  { mat = Triangle.mat A M* Triangle.mat B
  ; tri = λ i j j≤i → u∙v-zero  (row  i  (Triangle.mat A)) 
                                (col  j  (Triangle.mat B)) 
                                (one0-mat A B i j j≤i) 
  }
\end{code}
%if False
\begin{code}
  where  row : {m n : ℕ} → Fin m → Matrix m n → Vector n
         row i A = λ k → A i k
         col : {m n : ℕ} → Fin n → Matrix m n → Vector m
         col j B = λ k → B k j
\end{code}
%endif
To prove that upper triangular matrices form a ring, all we need to do is apply the matrix results to |Triangle.mat|.
