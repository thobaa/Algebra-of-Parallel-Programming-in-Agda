%if False
\begin{code}
open import Data.Nat
module Valiant.Splitting where
\end{code}
%endif
We call this datatype |Splitting|, since it indexes the splitting of the matrix, and define it as follows
\begin{code}
data Splitting : Set where
  one : Splitting
  bin : (s₁ : Splitting) → (s₂ : Splitting) → Splitting
\end{code}
where |one| plays the role of |suc zero| (since there's no reason to have dimensions $0$ for matrices, and |bin| plays the role of |+| (we have chosen the name \todo{change to bin in actual code} |bin| to connect it to binary trees: we can think of |ℕ| as the type of list with elements from |⊤|, where |⊤| is the one element type; then |Splitting| is the type of binary trees with elements |⊤|).

We also define the translation function that takes a |Splitting| to an element of |ℕ|, by giving the |one|-splitting the value |1| and summing the sub splittings otherwise:
\begin{code}
splitToℕ : Splitting → ℕ
splitToℕ one = 1
splitToℕ (bin s₁ s₂) = splitToℕ s₁ + splitToℕ s₂
\end{code}
