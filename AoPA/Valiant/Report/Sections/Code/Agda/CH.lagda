%if False
\begin{code}
module CH where
\end{code}
%endif
\subsection{The Curry Howard Correspondence}
To define a conjunction between two Propositions |P| and |Q|, one uses the pair |P × Q| defined below
%if False
\begin{code}
infixl 1 _,_
\end{code}
%endif
\begin{code}
data _×_ (P Q : Set) : Set where  
  _,_ : (p : P) → (q : Q) → P × Q
\end{code}
Because, to construct an element of |P × Q|, one needs an element of both |P| and |Q|.

For disjunction, one uses the disjoint sum |P + Q|:
\begin{code}
data _+_ (P Q : Set) : Set where
  inl : (p : P) → P + Q
  inr : (q : Q) → P + Q
\end{code}
For implication, one simply uses functions, |P → Q| [TODO: one???] % on its own line to distinguish it.
\begin{code}
impl : {P Q : Set} → P → Q
\end{code}
%if False
\begin{code}
postulate 
  secret : {P Q : Set} → P → Q
impl = secret
\end{code}
%endif
because implication in constructive logic is a method for converting a proof of |P| to a proof of |Q|¸ and this is exactly what a function is. On the other hand, one might want a data type for implication, along with constructors for ``canonical proofs'' \cite{dybj-or-ML}.
\begin{code}
data _⇒_ (P Q : Set) : Set where
  impl′ : (f : P → Q) → P ⇒ Q
\end{code}
However, this has the disadvantage that every time we want to access the function, we have to unwrap it, which clutters the code. In general, it's a good idea to use unwrapped functions when possible [TODO: other reason]. For example, we use this approach when defining the matrixes in \ref{Matrix-def}.

For universal quantification, we again use functions, but this time functions from the variables quantified over, |(x : X) → P x|:
\begin{code}
all : {X : Set} {P : X → Set} → (x : X) → P x
\end{code}
%if False
\begin{code}
postulate
  secret2 : {X : Set} {P : X → Set} → (x : X) → P x
all = secret2
\end{code}
%endif
Indeed, Agda allows the use of the syntax |∀ x| to mean |(x : _)| in type definitions, so that |∀ x → P x| means exactly what we expect it to mean (using the |∀ x| in definitions is nice even when not considering the types as propositions, because it lets us use Agda's type inference to shorten the definitions).

Finally, existential quantification, $\exists x. P(x)$, which in constructive logic is interpreted to be true if there is a pair $x_0$ along with a proof of $P (x_0)$, so we can model it by a dependent product (similar to the cartesian product defined above but now we consider one of the sets a domain for the variables, and the other as a proposition). We use the same name for the constructor as above.
\begin{code}
data ∃ (X : Set) (P : X → Set) : Set where
  _,_ : (x : X) → P x → ∃ X P
\end{code}



% labels to fill in.
\label{Matrix-def}
