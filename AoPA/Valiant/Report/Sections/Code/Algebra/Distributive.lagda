%if False
\begin{code}
module Algebra.Distributive where
open import Agda.CH
open import Algebra.Equivalence
\end{code}
%endif
In Agda, we begin by defining what a binary operation is:
\begin{code}
Op₂ : Set → Set
Op₂ A = A → A → A

postulate 
  X : Set
  _∙_ : X → X → X
  _≈_ : X → X → Set
  _⁻¹ : X → X
  e : X
Inverse : Set
Inverse = (∀ x → ((x ⁻¹) ∙ x) ≈ e) ∧ (∀ x → (x ∙ (x ⁻¹)) ≈ e)
Identity : Set
Identity = (∀ x → (e ∙ x) ≈ x) ∧ (∀ x → (x ∙ e) ≈ x)
\end{code}

%In Agda, we define the two requirements separately, as |_DistributesOverˡ_| and |_DistributesOverʳ_|, for left and right distributive repectively, so the statement that |*| distributes over |+| on the right becomes the very readable |* DistributesOverˡ +| (sadly, the definition cannot be written in this readable syntax due to the fact that we need to include an implicit argument to express equality):
\begin{code}
{-_DistributesOverˡ_ : {A : Set} {_≈_ : Rel A} → Op₂ A → Op₂ A → Set
_DistributesOverˡ_ {A} {_≈_} _*_ _+_ = ∀ x y z → (x * (y + z)) ≈ ((x * y) + (x * z))
_DistributesOverʳ_ : {A : Set} {_≈_ : Rel A} → Op₂ A → Op₂ A → Set
_DistributesOverʳ_ {A} {_≈_} _*_ _+_ = ∀ x y z → ((y + z) * x) ≈ ((y * x) + (z * x))-}
\end{code}
And then we combine them to make the proposition |_DistributesOver_|:
\begin{code}
{-
_DistributesOver_ : {A : Set} {_≈_ : Rel A} → Op₂ A → Op₂ A → Set
_DistributesOver_ {A} {_≈_} _*_ _+_ = (_DistributesOverˡ_ {A} {_≈_} _*_ _+_) ∧ (_DistributesOverʳ_ {A} {_≈_} _*_ _+_)
-}
\end{code}

