%if False
\begin{code}
open import Agda.List1
open import Agda.CH
module Agda.List2 where

\end{code}
%endif
We now go back to defining the |maxL| function. First, for convenience, we define a strictly less than relation:
\begin{code}
_<_ : ℕ → ℕ → Set
m < n = suc m ≤ n
\end{code}
We do not need to create a new datatype using |data| for this since we can use the fact that |m < n| should be equivalent to |suc m ≤ n|. In fact, with this definition, Agda will evaluate any occurence of |m < n| to |suc m ≤ n| internally, which helps us when we write proofs. 

Now, we can define the type of the |maxL| function. First, we give the type:
\begin{code}
maxL : (xs : [ ℕ ]) → (0 < length xs) → ℕ
\end{code}
That is, |maxL| takes a list of natural numbers |xs| and a proof that the length of |xs| is greater than zero and returns the maximum of the list. To define the function, we pattern match on the first argument:
\begin{code}
maxL [] ()
maxL (x ∷ []) _ = x
maxL (x ∷ (x′ ∷ xs)) _ = max x (maxL (x′ ∷ xs) (s≤s z≤n))
\end{code}
On the first line, we use the absurd pattern |()| to denote the empty case resulting from pattern matching on the proof (there are no cases when pattern matchin on an element of |1 ≤ 0|, and |()| is used to denote this, since Agda does not allow us to just leave out a case). On the second two lines, we do not care about what the input proof is (it is |s≤s z≤n| in both cases, so we write |_|, which takes the place of the variable but does not allow it to be used in the definition to signify that it is not important).

We also need an indexing function (to specify that |maxL xs _| is in the list), and again, we only define it for sensible inputs (nonempty lists). The simplest definition would probably be:
\begin{code}
index : ∀ {a} → (xs : [ a ]) → (n : ℕ) → (n < length xs) → a
index [] n ()
index (x ∷ xs) zero _ = x
index (x ∷ xs) (suc n) (s≤s m≤n) = index xs n m≤n
\end{code}
Where we need the proof in the last line, to call the |index| function recursively.

However, we can shorten the function definition by including the fact that the index is less than the length of the list by using a datatype that combines the index and the proof. One way to do this would be to use a dependent pair, which we define again, because we want it outside of the Curry--Howard correspondence:
\begin{code}
data Σ (A : Set) (B : A → Set) : Set where
  _,_ : (x : A) → B x → Σ A B 
\end{code}
The order these definitions should be done is, of course, first define |Σ|, then define |A ∧ B = Σ A (λ x → B)| and |∃ P = Σ _ P| (where the underscore is used to denote the fact that the first argument of |Σ| can be infered from the type of the second).

We can now use the Haskell notation |‼| for indexing:
\begin{spec}
_‼_ : ∀ {a} → (xs : [ a ]) → Σ ℕ (λ n → n < length xs) → a
[]         ‼  (n       , ())
(x ∷ xs)   ‼  (zero    , _)         = x
(x ∷ xs)   ‼  (suc n   , s≤s m≤n)   = xs ‼ (n , m≤n)
\end{spec}
\todo{THOMAS: note about standard library, maybe}
We note, however, that we do not really use the proof for anything important. This, along with the fact that |ℕ| is inductively defined (and the structure of the definition of |_≤_|) lets us use an even nicer formulation, where the proof is further embedded into the datatype we use.

We choose to define type family |Fin|, where |Fin n| containing the numbers less than |n|, using the simple fact that if $n = 1 + n'$, then $0 \le n$, and if $n = 1 + n'$ and $i \le n'$, then $1 + i \le n$:
\begin{code}
data Fin : ℕ → Set where
  fzero  : {n : ℕ} → Fin (suc n)
  fsuc   : {n : ℕ} → Fin n → Fin (suc n)
\end{code}
That is, |fzero| (representing |0|, but given a different name for clarity---it is not equal to the natural number |0|, they do not even have the same type) is less than any number of the form |suc n|, and for any number |i|, less than some number |n|, |fsuc i| is less than |suc n| (we can see this definition as instansiating the second argument of |_≤_| to |suc n|).
As with |_≤_|, the |ℕ| is on the right hand side of the colon since again, we are defining a type family.
One disadvantage of the choice of |Fin| is that we are not dealing with natural numbers, at all. Instead, we have to define functions like
\begin{code}
toℕ : {n : ℕ} → Fin n → ℕ
toℕ fzero     = zero
toℕ (fsuc i)  = suc (toℕ i)
\end{code}
and
\begin{code}
fromℕ : (n : ℕ) → Fin (suc n)
fromℕ zero     = fzero
fromℕ (suc y)  = fsuc (fromℕ y)
\end{code}
and prove that they do what we expect (like that |toℕ (fromℕ i)| equals |i|).

These two different ways of defining things will be used later when we define upper triangular matrixes as a datatype. 
When we represent matrixes abstractly (as functions from their indices) in Section \ref{Triangle} with the datatype |Triangle|, we do not have a nice inductive definition of them, so we have to use the pairing of a matrix and a proof that it is upper triangular.
In Section \ref{Tri}, on the other hand, we define the datatype |Tri| of a concrete representation of upper triangular matrices which have a built in ``proof'' that the matrix is triangular. Then, we do not need to worry about the proof when defining multiplication, for example. If our definition returns a |Tri|, then the result is upper triangular.

We now define the indexing function using |Fin|:
%if False
\begin{code}
infix 10 _‼_
\end{code}
%endif
\begin{code}
_‼_ : ∀ {a} → (xs : [ a ]) → (n : Fin (length xs)) → a
[]         ‼ ()
(x ∷ xs)   ‼ fzero    = x
(x ∷ xs)   ‼ fsuc i   = xs ‼ i
\end{code}

Now we can finally express our specification in Agda.
\begin{code}
max-greatest : (xs : [ ℕ ]) → (pf : 0 < length xs) → 
         ((n : Fin (length xs)) → xs ‼ n ≤ maxL xs pf)
\end{code}
To prove this property of the |maxL| function, we must produce an inhabitant of the above type. We do this in the next section. %This takes quite a bit of work is actually quite a substantial task.
\subsection{Proving the correctness}
We have made the list and the proof that the length is greater than $0$ implicit arguments because they can be infered from the resulting type |xs ‼ n ≤ maxL xs pf|. However, when we prove the lemma, we are going to need to pattern match on those arguments many times.

To prove a proposition in Agda, it is important to look at the structure of the proposition. Then one needs to determine which part of the proposition one should pattern match on. To do this, it is a good idea to have a plan for the proof.

We begin by formulating the proof informally. The main idea we use is pattern matching the index into the list, if it is $0$, we want to prove the simpler proposition that |x ≤ maxL (x ∷ xs) pf|, which we call |max-greatest-base|, because it is the base case in an induction on the index:
\begin{code}
max-greatest-base : {x : ℕ} {xs : [ ℕ ]} → x ≤ maxL (x ∷ xs) (s≤s z≤n)
\end{code}
On the other hand, if the index is $i + 1$, we must have that the list must has length at least $2$, we proceed by doing noting:
\begin{enumerate}
\item \label{Ex.List.Induction1} By induction, the $i$th element of the tail is less than the greatest element of the tail.
\item \label{Ex.List.Induction2} The $i$th element of the tail equals the $i + 1$th element of the list.
\item \label{Ex.List.Induction3} By the definition of |max|, |maxL (x ∷ (x′ ∷ xs)) pf| expands to |max x (maxL (x′ ∷ xs) pf′)|, and for any |x| and |y|, we have |y ≤ max x y|.
\end{enumerate}
To translate the induction case into Agda code, we need to introduce two new lemmas. By induction, we already know that Point \ref{Ex.List.Induction1} is true. Additionally, Agda infers Point \ref{Ex.List.Induction2}. However, we still need to prove the second part of Point \ref{Ex.List.Induction3}:
\begin{code}
max-increasing₂ : {m n : ℕ} → n ≤ max m n
\end{code}
Where the subscript $2$ refers to the fact that it is the second argument of |max| that is on the left hand side of the inequality. Finally, we need a way to piece together inequalities, if |i ≤ j| and |j ≤ k|, then |i ≤ k| (that is, |≤| is transitive):
\begin{code}
≤-trans : {i j k : ℕ} → i ≤ j → j ≤ k → i ≤ k
\end{code}

Now we begin proving these lemmas, beginning with |≤-trans|, since it does not depend on the others (all the other lemmas will require further sublemmas to prove). We pattern match on the first proof, |i ≤ j|. If it is |z≤n|, Agda infers that |i| is |0|, so the resulting proof if |z≤n|:
\begin{code}
≤-trans z≤n j≤k = z≤n
\end{code}
If it is |s≤s i′≤j′|, Agda infers that |i == suc i′|, and |j == suc j′|, and |i′≤j′| is a proof that |i′ ≤ j′|. We pattern match on the proof of |j ≤ k|, which must be |s≤s j′≤k′|, because |j| is |suc j′|. Hence, we can use induction to get a proof that |i′ ≤ k′|, and apply |s≤s| to that proof:
\begin{code}
≤-trans (s≤s i′≤j′) (s≤s j′≤k′) = s≤s (≤-trans i′≤j′ j′≤k′)
\end{code}

We continue by proving |max-increasing₂|, for this, we introduce a lemma: |≤-refl|, stating that for any |n|, |n ≤ n| (that is, |≤| is reflexive), which is very easy to prove (if |n == 0|, a proof is given by the constructor |z≤n|, and if |n == suc n′|, by induction, |n′ ≤ n′| and |s≤s| takes the proof of this to a proof that |n ≤ n|:
\begin{code}
≤-refl : {n : ℕ} → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl
\end{code}
Now we prove |max-increasing₂|.
%if False
\begin{code}
max-increasing₁ : {m n : ℕ} → m ≤ max m n
max-increasing₁ {zero} {y} = z≤n
max-increasing₁ {suc n} {zero} = ≤-refl
max-increasing₁ {suc n} {suc n′} = s≤s max-increasing₁
\end{code}
%endif
We do this by pattern matching on the second argument (because it is the one involved in the inequality, and depending on its value, we need different constructors for the inequality proof). If it is |zero|, we use the constructor |z≤n|, regardless of what the first argument is. If it is |suc n′|, we need to know what the first argument was, so we pattern match on it. If the first argument is |zero|, then, from the definition of |max|, we know that |max zero (suc n′) == suc n′|, so we want to prove that |suc n′ ≤ suc n′|, which we do by using the lemma |≤-refl| (we note here that we didn't actually need the fact that the second argument was non-zero). On the other hand, if the first argument is |suc m′|, we know by induction (we call |max-increasing₂| where we need to supply at least the first argument, since it doesn't appear anywhere, and hence Agda is unable to infer it) that |n′ ≤ max m′ n′|, so we use |s≤s| to get |suc n′ ≤ suc (max m′ n′)|, and from the definition of |max|, we (and more importantly Agda) get that |suc (max m′ n′) == max (suc m′) (suc n′)|, so we are in fact done.
\begin{code}
max-increasing₂ {m} {zero} = z≤n
max-increasing₂ {zero} {suc n′} = ≤-refl
max-increasing₂ {suc m′} {suc n′} = s≤s (max-increasing₂ {m′} {n′})
\end{code}
We also prove the similar proposition, |max-increasing₁ : {m n : ℕ} → m ≤ max m n|, that |max| is greater than its first argument, in essentially the same way (we pattern match first on the first argument instead).\todo{check that variable names are reasonably consistent}

Using |max-increasing₁| and |≤-refl|, we are able to prove the initial step in the induction proof, |max-greatest-base|. We pattern match on the remainter of the list, if it is |[]|, we need to show that |x ≤ x|, which is done with |≤-refl|, and if it is |x′ ∷ xs|, we need to prove that |x ≤ maxL (x ∷ (x′ ∷ xs)) pf|, and expanding this using the definition of |max|, we find that we need to prove that |x ≤ max x (maxL (x′ ∷ xs) pf′)|, which is exactly what |max-increasing₁| does.
\begin{code}
max-greatest-base {x} {[]} = ≤-refl
max-greatest-base {x} {x′ ∷ xs} = max-increasing₁
\end{code}
Finally, we are able to finish our proof of |max-greatest|. As we said above, we want to pattern match on the index, however, this is not possible to do right away, since the available constructors (if any) for |Fin (length xs)| depends on the length of |xs|. Therefore, we begin by pattern matching on the list. If the list is empty, we fill in the absurd pattern |()| for the proof that it is nonempty. Otherwise, we pattern match on the index. 
If the index is |fzero|, we use the initial step |max-greatest-base|, to prove that |x ≤ maxL (x ∷ xs) pf|. 
If the index is |fsuc i|, we pattern match on the tail of the list. If it is empty, we know that the index shouldn't have been |fsuc i|, because we'd have |i : Fin zero|, so we fill in |i| with the absurd pattern |()|.
The case we have left is when the list is |x ∷ (x′ ∷ xs)|, and the index is |fsuc i|. As we said above, we use induction to prove that |(x′ ∷ xs) ‼ i ≤ maxL (x′ ∷ xs) pf|. By the definition of |‼|, we have that
\begin{spec}
(x ∷ (x′ ∷ xs)) ‼ (fsuc i) == (x′ ∷ xs) ‼ i
\end{spec}
So by induction, |max-greatest i| proves that |(x ∷ (x′ ∷ xs)) ‼ (fsuc i) ≤ maxL (x′ ∷ xs) pf|, and additionally, from the definition of |max|, 
\begin{spec}
maxL (x ∷ (x′ ∷ xs)) pf == maxℕ x (maxL (x′ ∷ xs) pf′)
\end{spec}
So using |maxℕ-increasing₂|, and |≤-trans| to put things together, we get \todo{clean up the proofs ``pf'' that are input to max} the desired result:
\begin{code}
max-greatest [] () _
max-greatest (x ∷ xs) (s≤s z≤n) fzero = max-greatest-base {x} {xs}
max-greatest (x ∷ []) (s≤s z≤n) (fsuc ())
max-greatest (x ∷ (x′ ∷ xs)) (s≤s z≤n) (fsuc i) = ≤-trans (max-greatest _ _ i) (max-increasing₂ {x})
\end{code}







\subsection{Finish}
Now, we are able to finish our proof of the specification by putting together the parts of the two previous sections. 

If the list is empty, the proof would be an element of |1 ≤ 0|, and that type is empty, so we can put in the absurd patern |()|. On the other hand, if the list is |x ∷ xs|, we make a pair of the above proofs, and are done:
\begin{code}
--max-spec [] ()
--max-spec (x ∷ xs) (s≤s z≤n) = max-greatest , max-in-list
\end{code}

To end this example, we note that proving even simple (obvious) propositions in Agda takes quite a bit of work, and a lot of code, but generally not much thinking. After this extended example, we feel that we have illustrated most of the techniques that will be used later on in the report. As we wrote in the introduction to the section, we will often only give the types of the propositions, followed with the types of important lemmas and note what part of the arguments we pattern match on and in what order.

We also feel that we have illustrated the fact that proving something in Agda often requires a lot of code, but not much thinking, as the above proof essentially proceeds as one would intuitively think to prove the specification correct. Most of the standard concepts used are available in one form or another from the standard library, and we have attempted to keep our names consistent with it (the actual code given in later sections uses the standard library when possible, but we try to include simplified definitions in this report).


\todo{fix references below (only visible in source)}
\label{decidable-def}
