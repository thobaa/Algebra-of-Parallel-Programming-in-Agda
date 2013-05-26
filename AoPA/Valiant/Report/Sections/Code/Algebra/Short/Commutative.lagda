%if False
\begin{code}
module Algebra.Short.Commutative where
Commutative : {X : Set} → (X → X → Set) → (X → X → X) → Set
\end{code}
%endif
\begin{code}
Commutative _≈_ _∙_ = ∀ x y → (x ∙ y) ≈ (y ∙ x)
\end{code}
