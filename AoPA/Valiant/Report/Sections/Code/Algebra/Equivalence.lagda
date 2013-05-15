%if False
\begin{code}
module Algebra.Equivalence where
\end{code}
%endif
To define an equivalence relation in Agda, we first need to define what a relation (on a set) is. \todo{write about definition -- and think about whether it need s to be there as opposed to |A → A → Set|}
\begin{code}
Rel : Set → Set₁
Rel X = X → X → Set
\end{code}
Next, we need to define the axioms it should satisfy: reflexivity, symmetry and transitivity. The first thing to note is that they are all propositions (parametrized by a relation), so they should be functions from |Rel| to |Set| (which is where propositions live).
\begin{code}
Reflexive   : {X : _} → (_∼_ : Rel X) → Set
Symmetric   : {X : _} → (_∼_ : Rel X) → Set
Transitive  : {X : _} → (_∼_ : Rel X) → Set
Reflexive   _∼_  = ∀ {x}      → x ∼ x
Symmetric   _∼_  = ∀ {x y}    → x ∼ y → y ∼ x
Transitive  _∼_  = ∀ {x y z}  → x ∼ y → y ∼ z → x ∼ z
\end{code}
Then, we define the record |IsEquivalence|, for expressing that a relation is an equivalence relation (we use a record to be able to extract the three axioms with using names)
\begin{code}
record IsEquivalence {X : Set} (_∼_ : Rel X) : Set where
  field
    refl   : Reflexive   _∼_
    sym    : Symmetric   _∼_
    trans  : Transitive  _∼_
\end{code}
In the remainder of the report, we use the slightly more general |IsEquivalence| definition from the Agda Standard Library, because it lets us use the standard library modules for equational reasoning.
