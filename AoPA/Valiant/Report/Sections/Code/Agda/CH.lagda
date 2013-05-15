%if False
\begin{code}
open import Agda.List1
module Agda.CH where
infix 4 _≤_
\end{code}
%endif
\subsubsection{The Curry--Howard Correspondence}
To consider proofs and propositions in Agda, and to allow functions to depend on them and their existence, we make use of the Curry--Howard correspondence (for a longer, more detailed introduction to the Curry--Howard correspondence with Agda, see for example \cite{Dep-types-at-work}). It states that a proposition $P$ can be seen as the type containing all proofs of $P$. To prove $P$, then means to give an element of the type corresponding to $P$ (i.e., a proof of $P$).

%We identify the type of all small types |Set| with the set of all propositions.

To give an example of viewing propositions as types, we take a look at the proposition $m \le n$. In Agda, we make the following definition:
\begin{code}
data _≤_ : ℕ → ℕ → Set where
  z≤n : {n : ℕ}   → zero ≤ n
  s≤s : {m n : ℕ} → m ≤ n → suc m ≤ suc n
\end{code}
Here we note that we placed the types of the arguments to |_≤_| on the right hand side of the |:|. This is because we are defining a lot of types at the same time, the types |m ≤ n|, for every |m n : ℕ|. We see this from the fact that the two constructors produce elements of different types, |zero ≤ n| and |suc m ≤ suc n|, respectively.

If we have an element of type |m ≤ n|, it is either constructed by |z≤n|, which means that |m| is |zero|, so that the proposition $m \le n$ is true. Otherwise, it was constructed by |s≤s|, and we must have |m = suc m'|, |n = suc n'| for some |m'|, |n'| and an element of type |m' ≤ n'|. But then, the proposition $m' \le n'$ is true, and hence, again $m \le n$ is true. So providing an element of type |m ≤ n| means providing a proof that |m ≤ n|, and it seems like identifying propositions and (some) types makes sense. 

We now present the basic logical operations (as interpreted in constructive logic) that are done on propositions to generate new propositions, and their implementations in Agda, using syntax similar to the one used in logic, through the Curry--Howard correspondence.

To define a conjunction between two propositions |P| and |Q|, we use the pair, defined as
%if False
\begin{code}
--infixl 1 _∧_
--infixl 1 _,_
\end{code}
%endif
\begin{code}
data _∧_ (P Q : Set) : Set where  
  _,_ : P → Q → P ∧ Q
\end{code}
This coincides with the logical notion of a conjunction, which requires a proof of both conjuncts, because as seen above, to construct an element of |P ∧ Q|, one needs an element of each of |P| and |Q|.

For disjunction, we use a disjoint sum:
\begin{code}
data _∨_ (P Q : Set) : Set where
  inl : P → P ∨ Q
  inr : Q → P ∨ Q
\end{code}
The two constructors mean that we can construct an element of |P ∨ Q| we need either an element of |P| or of |Q|.

For implication, one simply uses functions, |P → Q|,
because implication in constructive logic means a method for converting a proof of |P| to a proof of |Q|¸ and this is exactly what a function is. 

The last of the predicate logic operations is negation. Constructively, the negation of a proposition means that the proposition implies falsity. To define this, we first define the empty type as a type with no constructors to represent falsity:
\begin{code}
data ⊥ : Set where
\end{code}
This can thus be seen as a proposition with no proof, which is exactly what falsity is.
We thus define negation by
\begin{code}
¬ : Set → Set
¬ P = P → ⊥
\end{code}

For convenience, we also define the true proposition |⊤|, as a set with one constructor
\begin{code}
data ⊤ : Set where
  tt : ⊤
\end{code}
To prove this proposition we simply use the element |tt|.

%% MOVE THIS 
MOVE THIS!!

To reason about the |maxL| function, we are going to want to do different things depending on if 
Constructively, the law of excluded middle---saying that for every proposition |P|, either |P| or |¬ P| is true---is not valid. However, there are propositions for which it is valid. %(trivially, for all true propositions). 
These are said to be \emph{decidable}, and are propositions for which there exists an algorithm producing either a proof of the proposition, or a proof of the negation. In Agda, if |X| is a collection of statements, we define this with a helper type |Dec X| that has two constructors, one taking a proof of an instance |x : X| and one a proof |¬x : ¬ X|\todo{what is it really that is decidable, proposition or relation (think a bit)}:
\begin{code}
data Dec (P : Set) : Set where
  yes  : P    → Dec P
  no   : ¬ P  → Dec P
\end{code}
Then, a set of propositions |P| is proven to be decidable if we have a function |P → Dec P|, that is, and algorithm that takes an arbitrary instance of |P| and decides whether it is true.
\begin{Example}
  One example of a decidable proposition is inequality between natural numbers, which we consider in Section \ref{extended-example-nat-ineq}, since, given two natural numbers, we can determine which is smaller by repeatedly subtracting $1$ from both until one is zero.
\end{Example}
\todo{expand above section (the Dec section) a bit}

Next we move on to define the quantifications (universal and existential) in predicate logic.
 
For universal quantification, we again use functions, but this time, dependent functions: If $P$ is a predicate on $X$ (a function that takes elements of $X$ to propositions $P(x)$), the proposition $\forall x. P(x)$ corresponds to the type |(x : X) → P x|, since to give a function of that time would mean providing a way to construct an element of |P x| (that is, a proof of $P(x)$) for every |x : X|, which is what $\forall x. P(x)$ means.
Agda includes the syntax |∀ x| for |(x : _)| in type definitions (where the underscore indicates that the type should be infered), so that |∀ x → P x| means exactly what we expect it to mean.

Finally, existential quantification, $\exists x. P(x)$, which in constructive logic is interpreted to be true if there is a pair $(x_0, P x_0)$ of a witness $x_0$ along with a proof of $P (x_0)$. So like for conjunction, we use a pair. But this time, the second element of the pair should depend on the first:
\begin{code}
data ∃ {X : Set} (P : X → Set) : Set where
  _,_ : (x : X) → P x → ∃ P
\end{code}
