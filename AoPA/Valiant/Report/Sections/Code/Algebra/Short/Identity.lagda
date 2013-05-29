%if False
\begin{code}

open import Data.Product using () renaming (_×_ to _∧_)
module Algebra.Short.Identity where
Identity : {X : Set} → (X → X → Set) →  X → (X → X → X) →  Set
--private postulate _∧_ : Set → Set → Set
--infix  
\end{code}
%endif
\begin{code}
Identity _≈_ e _∙_ = (∀ x → (e ∙ x) ≈ x) ∧ (∀ x → (x ∙ e) ≈ x)
\end{code}
We quantify over |x| in both conjuncts to make our code compatible with the Agda Standard Library and because the two conjuncts make sense as individual propositions: an element can be just a left identity or a right identity. It might be the case that some element |e| is only an inverse of |_∙_| when multiplied on the left, for example. The parentheses in the type are needed to give |∀| the correct scope.
