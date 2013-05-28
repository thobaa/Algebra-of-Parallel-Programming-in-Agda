%if False
\begin{code}
module Algebra.Short.Zero where
open import Data.Product using () renaming (_×_ to _∧_)
Zero : {X : Set} → (X → X → Set) → X → (X → X → X) → Set
\end{code}
%endif
In Agda, we give the proposition that |z| is a zero element as the conjunction
\begin{code}
Zero _≈_ z _∙_ = (∀ x → (z ∙ x) ≈ z) ∧ (∀ x → (x ∙ z) ≈ z)
\end{code}
