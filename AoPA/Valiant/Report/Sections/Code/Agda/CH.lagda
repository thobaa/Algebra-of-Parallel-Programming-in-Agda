%if False
\begin{code}
open import Agda.List1
module Agda.CH where
infix 4 _≤_
\end{code}
%endif
\section{The Curry--Howard Correspondence}
\label{CH}
To consider proofs and propositions in Agda, and to allow functions to depend on them and their existence, we use the Curry--Howard correspondence: propositions as types, proofs as programs (for a more detailed introduction to it, see for example \cite{DepTypAtWork}). The Curry--Howard correspondence states that a proposition $P$ can be seen as the type containing all ``proof objects'', of $P$ (we will refer to them simply as proofs in the remainder). To prove $P$ then means to give an element of the type corresponding to $P$ (i.e., a proof of $P$).

%We identify the type of all small types |Set| with the set of all propositions.

To give an example of viewing propositions as types, we take a look at the proposition ``|m| is at most |n|''. In Agda, we make the following definition:
%if False
\begin{code}
data _≤_ : ℕ → ℕ → Set where
  z≤n  : {n : ℕ}    → zero ≤ n
  s≤s  : {m n : ℕ}  → (m≤n : m ≤ n) → suc m ≤ suc n
\end{code}
%endif
\begin{spec}
data _≤_ : ℕ → ℕ → Set where
  z≤n : {n : ℕ}   → zero ≤ n
  s≤s : {m n : ℕ} → m ≤ n → suc m ≤ suc n
\end{spec}
Here we note the placement of the |ℕ|s in the first line. They are placed on the right side of the colon because they are indices of |_≤_|. This means that we are defining a type family (consisting of the types |m ≤ n| for every |m n : ℕ|. We can see that we need to do this from the fact that the two constructors produce elements of different types, |zero ≤ n| and |suc m ≤ suc n|, respectively. We also make note of the names we have given the constructors. In the remainder of this report, we often use the convention that |Pxy| (without the spaces) is the name of an element of datatype |P x y| (with spaces), so |m≤n| is a proof that |m ≤ n|.

If we have an element of type |m ≤ n| it is either constructed by |z≤n|, which means that |m| is |zero|, so that the proposition ``|m| is at most |n|'' is true. Or it is constructed by |s≤s|, and we must have |m = suc k|, |n = suc l| for some |k|, |l| and an element of type |k ≤ l|. But then, the proposition ``|k| is at most than |l|'' is true, and hence, again ``|m| is at most |n|'' is true. So providing an element of type |m ≤ n| means providing a proof that |m ≤ n|. Intuitively, we see that identifying propositions and types makes sense. 

We now present the logical operations (as interpreted in constructive logic) that are done on propositions to generate new propositions, and their implementations in Agda, using syntax similar to the one used in logic, through the Curry--Howard correspondence.

\subsection{Propositional logic}
We begin with concepts from propositional logic, and in the next section, we consider predicate logic.

To define a conjunction between two propositions |P| and |Q|, we use the pair, defined as
%if False
\begin{code}
--infixl 1 _∧_
--infixl 1 _c_
\end{code}
%endif
\begin{code}
data _∧_ (P Q : Set) : Set where  
  _c_ : P → Q → P ∧ Q
\end{code}
This coincides with the logical notion of a conjunction, which requires a proof of both conjuncts, because as seen above, to construct an element of |P ∧ Q|, one needs an element of each of |P| and |Q|.

For disjunction, we use a disjoint sum:
\begin{code}
data _∨_ (P Q : Set) : Set where
  inl  : P  → P ∨ Q
  inr  : Q  → P ∨ Q
\end{code}
The two constructors mean that to construct an element of |P ∨ Q| we need either an element of |P| or of |Q|.

For implication, one simply uses functions, |P → Q|,
because implication in constructive logic means a method for converting a proof of |P| to a proof of |Q|, and this is exactly what a function is. 

The last predicate logic operation is negation. Constructively, the negation of a proposition means that the proposition implies falsity. We use the empty type to represent falsity:
\begin{code}
data ⊥ : Set where
\end{code}
This can thus be seen as a proposition with no proof, which is exactly what falsity is.
We then define negation by
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

\subsection{Predicate logic}
Now we move on to define the quantifiers (universal and existential) in predicate logic.
 
For universal quantification, we again use functions, but this time, dependent functions: If $P$ is a predicate on $X$ (a function that takes elements of $X$ to propositions $P(x)$), the proposition $\forall x. P(x)$ corresponds to the type |(x : X) → P x|, since to give a function of that type would mean providing a way to construct an element of |P x| (that is, a proof of $P(x)$) for every |x : X|, which is what $\forall x. P(x)$ means.
Agda includes the syntax |∀ x| for |(x : _)| in type definitions (where the underscore indicates that the type should be inferred), so that |∀ x → P x| means exactly what we expect it to mean.

Finally, existential quantification, $\exists x. P(x)$, which in constructive logic is interpreted to be true if there is a pair $(x_0, P x_0)$ of a witness $x_0$ along with a proof of $P (x_0)$. Like for conjunction, we use a pair. But this time, the second element of the pair depends on the first:
\begin{code}
data ∃ {X : Set} (P : X → Set) : Set where
  _c_ : (x : X) → P x → ∃ P
\end{code}
%We also note that if $P$ is a sentence containing $x$, the sentence $\exists x. P(x)$ where we quantify over $x$ would be written as 
%\begin{spec}
%∃ λ x → P x
%\end{spec}
%in Agda (we introduce an anonymous function |λ x → P x|, taking |x| to |P x| using lambda notation).

\subsection{Decidability}
Finally we discuss decidable propositions. Constructively, the law of excluded middle---saying that for any proposition $P$, $P \lor \lnot P$ is true---is not valid. There is no algorithm that takes an arbitrary proposition and returns either a proof of it, or a proof that it implies $\bot$. However, there are many propositions for which it is valid. These propositions are said to be \emph{decidable}. In Agda, if |P| is a proposition, we define the proposition that |P| is decidable as |Dec P|:
\begin{code}
data Dec (P : Set) : Set where
  yes  :    P  → Dec P
  no   : ¬  P  → Dec P
\end{code}
So an element of |Dec P| is a proof that |P| is decidable, since it contains either a proof of |P| or a proof of |¬  P|.

An example of a proposition that is decidable is the proposition that |m ≤ n|, where |m| and |n| are natural numbers. To prove that this is decidable for any |m| and |n|, we give a function that takes |m| and |n| and returns an element of |Dec (m ≤ n)|:
\begin{code}
_≤?_ : (m n : ℕ) → Dec (m ≤ n)
\end{code}
We present this function case by case. If |m| is |0|, we can construct a proof that |m ≤ n| with the constructor |z≤n|: 
\savecolumns
\begin{code}
0        ≤?  n  = yes z≤n
\end{code}
if |m| is |suc k|, we pattern match on |n|. If |n| is |0|, there is no proof of |m ≤ n|, since no constructor of |_≤_| constructs an element of type |suc k ≤ 0|. The fact that there are no such proofs is denoted by |λ ()| (we basically write an anonymous function of type |(suc k ≤ 0) → ⊥| by pattern matching on the empty type |suc k ≤ 0|).
\restorecolumns
\begin{code}
suc k   ≤?  0  = no (λ ())
\end{code}
If |n| is |suc l|, we use a |with| statement to add an extra argument to the function, to pattern match on |Dec (k ≤ l)|, which is decidable by induction:
\restorecolumns
\begin{code}
suc k   ≤?  suc l with k ≤? l 
suc k   ≤?  suc l | yes k≤l  = yes  (s≤s k≤l)
suc k   ≤?  suc l | no ¬k≤l  = no   (λ sm≤sn → ¬k≤l (p≤p sm≤sn))
  where  p≤p : {m n : ℕ} → suc m ≤ suc n → m ≤ n 
         p≤p (s≤s m≤n) = m≤n
\end{code}

