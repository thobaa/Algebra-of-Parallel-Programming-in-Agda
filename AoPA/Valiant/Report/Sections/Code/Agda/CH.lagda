%if False
\begin{code}
module CH where
\end{code}
%endif
\subsection{The Curry--Howard Correspondence}
To define a conjunction between two Propositions |P| and |Q|, one uses the pair |P ∧ Q| defined below
%if False
\begin{code}
infixl 1 _,_
\end{code}
%endif
\begin{code}
data _∧_ (P Q : Set) : Set where  
  _,_ : (p : P) → (q : Q) → P ∧ Q
\end{code}
Because, to construct an element of |P ∧ Q|, one needs an element of both |P| and |Q|.

For disjunction, one uses a disjoint sum:
\begin{code}
data _∨_ (P Q : Set) : Set where
  inl : (p : P) → P ∨ Q
  inr : (q : Q) → P ∨ Q
\end{code}
For implication, one simply uses functions, |P → Q|,
because implication in constructive logic is a method for converting a proof of |P| to a proof of |Q|¸ and this is exactly what a function is. On the other hand, one might want a data type for implication, along with constructors for ``canonical proofs'' \cite{dybj-or-ML}.
\begin{code}
data _⇒_ (P Q : Set) : Set where
  impl : (P → Q) → P ⇒ Q
\end{code}
However, this has the disadvantage that every time we want to access the function, we have to unwrap it, which clutters the code. In general, it's a good idea to use unwrapped functions when possible \todo{is there another reason}. For example, we use this approach when defining the matrixes in \ref{Matrix-def}.

The last of the predicate logic concepts is negation. Constructively, the negation of a proposition means that the proposition implies falsity. To define this, we first define the empty type as a type with no constructors to represent falsity:
\begin{code}
data ⊥ : Set where
\end{code}
We then define negation with
\begin{code}
¬ : (P : Set) → Set
¬ P = P → ⊥
\end{code}

Constructively, the law of excluded middle---saying that for every proposition |P|, either |P| or |¬ P| is true---is not valid. However, there are propositions for which it is valid (trivially, for all true propositions). These are said to be \emph{decidable}, and are propositions such that there exists an algorithm producing either a proof of the proposition, or a proof of the negation. In Agda, if |X| is a collection of statements, we define this with a helper type |Dec X| that has two constructors, one taking a proof of an instance |x : X| and one a proof |¬x : ¬ X|\todo{what is it really that is decidable, proposition or relation (think a bit)}:
\begin{code}
data Dec (P : Set) : Set where
  yes : ( p :   P) → Dec P
  no  : (¬p : ¬ P) → Dec P
\end{code}
Then, a set of propositions |P| is proven to be decidable if we have a function |P → Dec P|, that is, and algorithm that takes an arbitrary instance of |P| and decides whether it is true.
\begin{Example}
  One example of a decidable proposition is inequality between natural numbers, which we consider in Section \ref{extended-example-nat-ineq}, since, given two natural numbers, we can determine which is smaller by repeatedly subtracting $1$ from both until one is zero.
\end{Example}
\todo{expand above section (the Dec section) a bit}

Next (the \todo{CUrry or Howard? (or is this something I imagined I heard someone say?)} part of the Curry--Howard correspondence), we look at universal and existential quantification from predicate logic.
 
For universal quantification, we again use functions, but this time the variable is bound to a name |x : X|, and appears again, and the proposition can depend on the value |x|: |P : X → Set|, that is universal quantification is a function |(x : X) → P x|:
\begin{code}
all : {X : Set} {P : X → Set} → Set
all {X} {P} = (x : X) → P x
\end{code}
That is, for any element |x : X|, we have |P x|. Agda allows the use of the syntax |∀ x| to mean |(x : _)| in type definitions, so that |∀ x → P x| means exactly what we expect it to mean (using the |∀ x| in definitions is nice even when not considering the types as propositions, because it lets us use Agda's type inference to shorten the definitions).

Finally, existential quantification, $\exists x. P(x)$, which in constructive logic is interpreted to be true if there is a pair $(x_0, P x_0)$ of an element  $x_0$ along with a proof of $P (x_0)$, so we can model it by a dependent pair (similar to the cartesian product defined above but now we consider one of the sets a domain for the variables, and the other as a proposition). We use the same name for the constructor as above.
\todo{lookup ∃ in standard library}
\begin{code}
data ∃ {X : Set} (P : X → Set) : Set where
  _,_ : (x : X) → P x → ∃ P
\end{code}



% labels to fill in.
\todo{Fix the below labels (move)}
\label{Matrix-def}
\label{extended-example-nat-ineq}
