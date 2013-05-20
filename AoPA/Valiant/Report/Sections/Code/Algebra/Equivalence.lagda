%if False
\begin{code}
module Algebra.Equivalence where
\end{code}
%endif
To define an equivalence relation in Agda, we first recall that a relation (on a single set |X|) is an element of type |X → X → Set|. That is, it takes two elements of |X| and produces the proposition (recall that propositions are types) that the elements are related.

Next, we give the types for the propositions it should satsify. Given a relation |_∼_|, reflexivity is given by the type
\begin{spec}
|∀ {x} → x ∼ x|
\end{spec}
symmetry by the type
\begin{spec}
∀ {x y} → x ∼ y → y ∼ x
\end{spec}
and transitivity by
\begin{spec}
∀ {x y z} → x ∼ y → y ∼ z → x ∼ z
\end{spec}
That we decide to make the arguments |x|, |y| and |z| implicit is somewhat arbitrary, they can be inferred from the types appearing later, and we follow the definitions from the standard library.

Then, we define the record |IsEquivalence|, for expressing the proposition that a relation is an equivalence relation (we use a record so that we can give names to the three axioms, for use in proofs)
\begin{code}
record IsEquivalence {X : Set} (_∼_ : X → X → Set) : Set where
  field
    refl   : ∀ {x}      → x ∼ x
    sym    : ∀ {x y}    → x ∼ y → y ∼ x
    trans  : ∀ {x y z}  → x ∼ y → y ∼ z → x ∼ z
\end{code}
In the remainder of the report, we actually use the slightly more general |IsEquivalence| definition in the Agda Standard Library, because it lets us use the |EqReasoning| module from the Standard Library modules for equational reasoning, as examplified in Section \ref{EqReasoning}.
