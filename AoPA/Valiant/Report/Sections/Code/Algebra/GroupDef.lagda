%if False
\begin{code}
module Algebra.GroupDef where
open import Algebra.Equivalence
open import Agda.CH
\end{code}
%endif
\begin{code}
record IsGroup {G : Set} (_≈_ : G → G → Set) (_∙_ : G → G → G) (e : G) (_⁻¹ : G → G) : Set where
  field
    isEquivalence  : IsEquivalence _≈_
    assoc          : ∀ x y z → ((x ∙ y) ∙ z) ≈ (x ∙ (y ∙ z))
    ∙-cong         : ∀ {x x' y y'} → x ≈ x' → y ≈ y' → (x ∙ y) ≈ (x' ∙ y')
    identity       : (∀ x → (e ∙ x) ≈ x) ∧ (∀ x → (x ∙ e) ≈ x)
    inverse        : (∀ x → (x ⁻¹ ∙ x) ≈ e) ∧ (∀ x → (x ∙ (x ⁻¹)) ≈ e)
    ⁻¹-cong        : ∀ {x x'} → x ≈ x' → x ⁻¹ ≈ x' ⁻¹
\end{code}


\begin{code}
record Group : Set₁ where
  infix 7 _∙_
  infix 4 _≈_
  field
    Carrier  : Set
    _≈_      : Carrier → Carrier → Set
    _∙_      : Carrier → Carrier → Carrier
    e        : Carrier
    _⁻¹      : Carrier → Carrier
    isGroup  : IsGroup _≈_ _∙_ e _⁻¹
\end{code}
Where we have both defined the various elements required in a group, along with the axioms they need to satisfy (which are hidden in |IsGroup|). To be able to use the group for reasoning, we open the ``module'' |IsGroup|:
\begin{code}
  open IsGroup isGroup public
\end{code}
This way, if we open the record |Group|, we have immediate access to the corresponding record |IsGroup|.

If we are to prove that something (a collection of an equivalence relation, an operation and a function) is a group, we prove |IsGroup|. Additionally, 
