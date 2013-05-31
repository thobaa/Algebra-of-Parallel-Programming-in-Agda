%if False
\begin{code}
open import Data.Nat
module Valiant.Splitting where
\end{code}
%endif
We define such a datatype and call |Splitting|, since it determines the splitting of the matrix, and define it as follows
\begin{code}
data Splitting : Set where
  one  : Splitting
  bin  : Splitting → Splitting → Splitting
\end{code}
where |one| plays the role of |suc zero| (since there is no reason to have dimensions $0$ for matrices, and |bin| plays the role of |_+_| (we have chosen the name |bin| to connect it to binary trees: we can think of |ℕ| as the type of list with elements the one element type, then |Splitting| is the type of binary trees with elements from the one element type).

We can define the translation function that takes a |Splitting| to an element of |ℕ|, by giving the |one|-splitting the value |1| and summing the sub splittings otherwise:
\begin{code}
splitToℕ : Splitting → ℕ
splitToℕ one          = 1
splitToℕ (bin s₁ s₂)  = splitToℕ s₁ + splitToℕ s₂
\end{code}
