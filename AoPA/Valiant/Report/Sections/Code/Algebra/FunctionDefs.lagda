%if False
\begin{code}
module FunctionDefs where
\end{code}
%endif
We now define the different lemmas involved (note that to use the file, this needs to happen before the lemmas are referred to in |IsGroup|. 
\begin{Def}
  A relation $R \subset X \times X$ is called an \emph{equivalence relation} if it is
  \begin{itemize}
  \item Reflexive: for $x \in X$, $x R x$.
  \item Symmetric: for $x$, $y \in X$, if $x R y$, then $y R x$.
  \item Transitive: for $x$, $y$, $z \in X$, if $x R y$ and $y R z$, then $x R z$.
  \end{itemize}
\end{Def}
An equivalence relation behaves like ``equality'' in the following sense:
\begin{Proposition}
An equivalence relation partitions the elements of a set into disjoint equivalence classes.
\end{Proposition}
, in that it partitions elements of a set into subset of equivalence classes, and things  so much so that an equivalence relation can be used to define what ``equality'' means on a set, and this is exactly what we do in the definition of a |IsGroup|.

\todo{Expand on induced equality from equivalence classes.}

In Agda, we implement this as a record (we give the relation the name |_≈_| to further connect it with equality):
\begin{code}
record IsEquivalence {A : Set} (_≈_ : A → A → Set) : Set where
  field
    refl  : {a : A} → a ≈ a
    sym   : {a b : A} → a ≈ b → b ≈ a
    trans : {a b c : A} → a ≈ b → b ≈ c → a ≈ c
\end{code}

