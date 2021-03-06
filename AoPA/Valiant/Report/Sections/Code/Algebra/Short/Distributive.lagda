%if False
\begin{code}
module Algebra.Short.Distributive where
--private postulate _∧_ : Set → Set →  Set
open import Data.Product using () renaming (_×_ to _∧_)
Distributive : {X : Set} → (X → X → Set) → (X → X → X) → (X → X → X) → Set
\end{code}
%endif
In Agda, given binary operations |_+_| and |_∙_|, we define the proposition that |_∙_| distributes over |_+_|, with respect to a given equivalence relations |_≈_| as follows:
\begin{code}
Distributive _≈_ _∙_ _+_ =  (∀ x y z → (x ∙ (y + z)) ≈ ((x ∙ y) + (x ∙ z)))
                            ∧ 
                            (∀ x y z → ((y + z) ∙ x) ≈ ((y ∙ x) + (z ∙ x)))
\end{code}
In the Agda Standard Library, the module containing the function properties is parametrised by an equivalence relation, so the properties do not need the argument |_≈_|. Instead of |Distributive|, the property is called |_DistributesOver_| in the standard library, giving it a very readable syntax.
