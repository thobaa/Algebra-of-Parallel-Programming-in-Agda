%if False
\begin{code}
module Algebra.Short.Associative where
Associative : {X : Set} → (X → X → Set) → (X → X → X) → Set
\end{code}
%endif
\begin{code}
Associative _≈_ _∙_ = ∀ x y z → (x ∙ (y ∙ z)) ≈ ((x ∙ y) ∙ z)
\end{code}
