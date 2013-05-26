%if False
\begin{code}
module Algebra.Short.Inverse where

private postulate _∧_ : Set → Set → Set
Inverse : {X : Set} → (X → X → Set) → (X → X) → X → (X → X → X) →  Set
\end{code}
%endif
\begin{code}
Inverse _≈_  _⁻¹ e _∙_ = (∀ x → ((x ⁻¹) ∙ x) ≈ e) ∧ (∀ x → (x ∙ (x ⁻¹)) ≈ e)
\end{code}
