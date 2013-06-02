%if False
\begin{code}
module Algebra.Equivalence where
Reflexive : {X : Set} → (X → X → Set) → Set
Transitive : {X : Set} → (X → X → Set) → Set
Symmetric : {X : Set} → (X → X → Set) → Set
\end{code}
%endif
To define an equivalence relation in Agda, use the fact that a relation (on a single set |X|) is an element of type |X → X → Set|. That is, it takes two elements of |X| and produces the proposition (recall that propositions are types) that the elements are related.

Next, we give the types for the propositions it should satisfy. Given a relation |_∼_|, reflexivity is given by the type
\begin{code}
Reflexive _∼_ = ∀ {x} → x ∼ x
\end{code}
symmetry by the type
\begin{code}
Symmetric _∼_ = ∀ {x y} → x ∼ y → y ∼ x
\end{code}
and transitivity by
\begin{code}
Transitive _∼_ = ∀ {x y z} → x ∼ y → y ∼ z → x ∼ z
\end{code}
That we decide to make the arguments |x|, |y| and |z| implicit is somewhat arbitrary, they can be inferred from the types appearing later, and we follow the definitions from the Standard Library.

Then, we define the record |IsEquivalence|, for expressing the proposition that a relation is an equivalence relation (we use a record so that we can give names to the three axioms, for use in proofs)
\begin{code}
record IsEquivalence {X : Set} (_∼_ : X → X → Set) : Set where
  field
    refl   : Reflexive   _∼_
    sym    : Symmetric   _∼_ 
    trans  : Transitive  _∼_
\end{code}
In the remainder of the report, we actually use the slightly more general |IsEquivalence| definition in the Agda Standard Library, because it lets us use the |EqReasoning| module from the Standard Library for equational reasoning, as exemplified in Section \ref{Section-where-eqr-helper-is-defined}.
