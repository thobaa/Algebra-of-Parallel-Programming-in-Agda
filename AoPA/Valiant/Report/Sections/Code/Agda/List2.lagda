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
maxL []               ()
maxL (x ∷ [])         _ = x
maxL (x ∷ (x' ∷ xs))  _ = max x (maxL (x' ∷ xs) (s≤s z≤n))
\end{code}
On the first line, we use the absurd pattern |()| to denote the empty case resulting from pattern matching on the proof (there are no cases when pattern matchin on an element of |1 ≤ 0|, and |()| is used to denote this, since Agda does not allow us to just leave out a case). On the second two lines, we do not care about what the input proof is (it is |s≤s z≤n| in both cases, so we write |_|, which takes the place of the variable but does not allow it to be used in the definition to signify that it is not important).

We also need an indexing function (to specify that |maxL xs _| is in the list), and again, we only define it for sensible inputs (nonempty lists). The simplest definition would probably be:
\begin{code}
index : ∀ {a} → (xs : [ a ]) → (i : ℕ) → (i < length xs) → a
index []        i        ()
index (x ∷ xs)  0        _         = x
index (x ∷ xs)  (suc i)  (s≤s m≤n) = index xs i m≤n
\end{code}
Where we need the proof in the last line, to call the |index| function recursively.

However, we can shorten the function definition by including the fact that the index is less than the length of the list by using a datatype that combines the index and the proof. This datatype is known as |Fin|, where |Fin n| contains the set of all natural numbers strictly less than |n|. One way to define |Fin| would be to use a dependent pair, which we define again to give it a syntax for types (as opposed to the ``logical'' |∃|):
\begin{code}
data Σ (A : Set) (B : A → Set) : Set where
  _,_ : (x : A) → B x → Σ A B 
\end{code}
The order these definitions should be done is, first define |Σ|, then define |A ∧ B = Σ A (λ x → B)| and |∃ P = Σ _ P|, where the underscore is used to denote the fact that the first argument of |Σ| can be infered from the type of the second.
Then, we could define |Fin| as:
\begin{spec}
Fin : ℕ → Set
Fin n = Σ ℕ (λ i → i < n)
\end{spec}
We can now use the Haskell notation |‼| for indexing:
\begin{spec}
_‼_ : ∀ {a} → (xs : [ a ]) → Fin (length xs) → a
[]         ‼  (i       , ())
(x ∷ xs)   ‼  (0       , _)         = x
(x ∷ xs)   ‼  (suc i   , s≤s m≤n)   = xs ‼ (i , m≤n)
\end{spec}
We note, however, that we do not really use the proof part for anything important. This, along with the fact that |ℕ| is inductively defined (and the structure of the definition of |_≤_|) lets us use an even nicer formulation, where the proof is further embedded into the datatype we use.

Instead, we choose to define |Fin| as a type family, using the simple fact that if $n = 1 + k$, then $0 \le n$, and if $n = 1 + k$ and $i \le k$, then $1 + i \le n$:
\begin{code}
data Fin : ℕ → Set where
  f0     : {n : ℕ} → Fin (suc n)
  fsuc   : {n : ℕ} → Fin n → Fin (suc n)
\end{code}
That is, |f0| (representing |0|, but given a different name for clarity---it is not equal to the natural number |0|, they do not even have the same type) is less than any number of the form |suc n|, and for any number |i|, less than some number |n|, |fsuc i| is less than |suc n| (we can see this definition as instantiating the second argument of |_≤_| to |suc n|).
As with |_≤_|, the |ℕ| is on the right hand side of the colon since because we are defining a type family.
One disadvantage of the choice of |Fin| is that we are not dealing with natural numbers, at all. Instead, we have to define functions like
\begin{code}
toℕ : {n : ℕ} → Fin n → ℕ
toℕ f0        = 0
toℕ (fsuc i)  = suc (toℕ i)
\end{code}
and
\begin{code}
fromℕ : (n : ℕ) → Fin (suc n)
fromℕ 0        = f0
fromℕ (suc y)  = fsuc (fromℕ y)
\end{code}
and prove that they do what we expect (like that |toℕ (fromℕ i)| equals |i|).

These two different ways of defining things will be used later when we define upper triangular matrices as a datatype. 
When we represent matrices abstractly (as functions from their indices) in Section \ref{Triangle} with the datatype |Triangle|, we do not have a nice inductive definition of them, so we have to use the pairing of a matrix and a proof that it is upper triangular.
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
(x ∷ xs)   ‼ f0       = x
(x ∷ xs)   ‼ fsuc i   = xs ‼ i
\end{code}

Now we can finally express our specification in Agda.
\begin{code}
max-greatest : (xs : [ ℕ ]) → (pf : 0 < length xs) → 
         (i : Fin (length xs)) → xs ‼ i ≤ maxL xs pf
\end{code}
To prove this property of the |maxL| function, we must produce an inhabitant of the above type. We do this in the next section. %This takes quite a bit of work is actually quite a substantial task.
\subsection{Proving the correctness}
To prove a proposition in Agda, it is important to look at the structure of the proposition. Then one needs to determine which part of the proposition one should pattern match on. To do this, it is a good idea to have a plan for the proof.

We formulate the proof informally. The main idea we use is pattern matching the index into the list, if it is $0$, we want to prove the simpler proposition that |x ≤ maxL (x ∷ xs) pf|, which we call |max-greatest-base|, because it is the base case in an induction on the index:
\begin{code}
max-greatest-base : (x : ℕ) (xs : [ ℕ ]) → x ≤ maxL (x ∷ xs) (s≤s z≤n)
\end{code}
On the other hand, if the index is $i + 1$, the list has length at least $2$, and we proceed by noting:
\begin{enumerate}
\item \label{Ex.List.Induction1} By induction, the $i$th element of the tail is less than the greatest element of the tail.
\item \label{Ex.List.Induction2} The $i$th element of the tail equals the $(i + 1)$th element of the list.
\item \label{Ex.List.Induction3} By the definition of |maxL|, we get that |maxL (x ∷ (x' ∷ xs)) pf| reduces to |max x (maxL (x' ∷ xs) pf')|, and for any |x| and |y|, we should have |y ≤ max x y|.
\end{enumerate}
To translate the induction case into Agda code, we need to introduce two new lemmas. By induction, we already know that Point \ref{Ex.List.Induction1} is true. Additionally, Agda infers Point \ref{Ex.List.Induction2}, so there is nothing to prove. However, we still need to prove the second part of Point \ref{Ex.List.Induction3}:
\begin{code}
max-≤₂ : {m n : ℕ} → n ≤ max m n
\end{code}
Where the subscript |₂| refers to the fact that it is the second argument of |max| that is on the left hand side of the inequality. Then, to combine the three points, we need a way to piece together inequalities, if |i ≤ j| and |j ≤ k|, then |i ≤ k| (i.e., |_≤_| is transitive, see Section \ref{Intro-defs}):
\begin{code}
≤-trans : {i j k : ℕ} → i ≤ j → j ≤ k → i ≤ k
\end{code}

Now we begin proving these lemmas, starting with |≤-trans| as it does not depend on the others (all the other lemmas will require further sub-lemmas to prove). We pattern match on the first proof, |i ≤ j|. If it is |z≤n|, Agda infers that |i| is |0|, so the resulting proof if |z≤n|:
\savecolumns
\begin{code}
≤-trans  z≤n          j≤k          = z≤n
\end{code}
If it is |s≤s a≤b|, Agda infers that |i| is |suc a|, and |j| is |suc b| for some |a|, |b|, where |a≤b| is a proof that |a ≤ b|. We then pattern match on the proof of |j ≤ k|, which has to be |s≤s b≤c| since |j| is |suc b|. Hence, we can use induction to get a proof that |a ≤ c|, and apply |s≤s| to that proof:
\restorecolumns
\begin{code}
≤-trans  (s≤s a≤b)    (s≤s b≤c)    = s≤s (≤-trans a≤b b≤c)
\end{code}
and we are done.

We also introduce another lemma about |_≤_|: |≤-refl|, stating that for any |n|, |n ≤ n| (i.e., |_≤_| is reflexive, see Section \ref{Intro-defs}), which is very easy to prove (if |n| is |0|, a proof is given by the constructor |z≤n|, and if |n| is |suc m|, by induction, we find a proof of |m ≤ m| and |s≤s| takes that proof to a proof that |n ≤ n|:
\begin{code}
≤-refl : {n : ℕ} → n ≤ n
≤-refl  {0}      = z≤n
≤-refl  {suc n}  = s≤s ≤-refl
\end{code}
Now we prove |max-≤₂|.
We pattern matching on the second argument. If it is |0|, we use the constructor |z≤n|, regardless of what the first argument is:
\savecolumns
\begin{code}
max-≤₂  {m}      {0}       = z≤n
\end{code}
If it is |suc l|, we pattern match on the first argument. If it is |0|, then, |max 0 (suc l)| reduces to |suc l|, so we prove |suc l ≤ suc l| using |≤-refl| (we can note that we did not actually need the fact that the second argument was non-zero, since |max 0 n| reduces to |n| no matter what |n| is):
\restorecolumns
\begin{code}  
max-≤₂  {0}      {suc l}   = ≤-refl
\end{code}
On the other hand if the first argument is |suc k|, we find a proof of |l ≤ max k l| using |max-≤₂|---we need to supply the first implicit argument which Agda is unable to infer---and use |s≤s| on it to get |suc l ≤ suc (max k l)|, which Agda reduces |max (suc k) (suc l)| to |suc (max k l)|, and we are done:
\restorecolumns
\begin{code}
max-≤₂  {suc k}  {suc l}   = s≤s (max-≤₂ {k})
\end{code}
We also prove the similar proposition, that |max| is greater than its first argument, in essentially the same way (we pattern match first on the first argument instead, and this time, Agda is able to infer the arguments of |max-≤₁| in the induction case, so we leave them out):
\begin{code}
max-≤₁ : {m n : ℕ} → m ≤ max m n
max-≤₁  {0}       {n}        = z≤n
max-≤₁  {suc k}   {0}        = ≤-refl
max-≤₁  {suc k}   {suc l}    = s≤s max-≤₁
\end{code}

Using |max-≤₁| and |≤-refl|, we are able to prove the initial step in the induction proof, |max-greatest-base|. We pattern match on |xs|. If it is |[]|, we need to show that |x ≤ x|, which we do with |≤-refl|, again:
\savecolumns
\begin{code}
max-greatest-base  x  []         = ≤-refl
\end{code}
If it is |x' ∷ xs|, we need to prove that |x ≤ maxL (x ∷ (x' ∷ xs)) _|. Agda reduces the right hand side to |max x (maxL (x' ∷ xs) _)|, so we just need to use |max-≤₁| does:
\restorecolumns
\begin{code}
max-greatest-base  x  (x' ∷ xs)  = max-≤₁
\end{code}

Finally, we finish our proof, |max-greatest|. As we said above, we want to pattern match on the index, however, this is not possible to do right away, since the available constructors (if any) for |Fin (length xs)| depends on the length of |xs|. Therefore, we begin by pattern matching on the list. If the list is empty, we fill in the absurd pattern |()| for the proof that it is nonempty:
\savecolumns
\begin{code}
max-greatest  []                 ()         _
\end{code}
Otherwise, |Fin (length xs)| is non-empty, and can pattern match on the index.
If the index is |f0|, we use the initial step |max-greatest-base|, to prove that |x ≤ maxL (x ∷ xs) pf|:
\restorecolumns
\begin{code}
max-greatest  (x ∷ xs)           (s≤s z≤n)  f0          =  max-greatest-base x xs
\end{code}
If the index is |fsuc i|, we pattern match on the tail of the list. If it is empty, we know that the index cannot be |fsuc i|, because we would have |i : Fin 0|, so we fill in |i| with the absurd pattern |()|:
\restorecolumns
\begin{code}
max-greatest  (x ∷ [])           (s≤s z≤n)  (fsuc ())
\end{code}
The last case is when the list is |x ∷ (x' ∷ xs)|, and the index is |fsuc i|. As we said above, we use induction to prove that |(x' ∷ xs) ‼ i ≤ maxL (x' ∷ xs) _|. By the definition of |‼|, |(x ∷ (x' ∷ xs)) ‼ (fsuc i)| reduces to |(x' ∷ xs) ‼ i|.
So by induction, |max-greatest i| proves that |(x ∷ (x' ∷ xs)) ‼ (fsuc i) ≤ maxL (x' ∷ xs) pf|. From the definition of |maxL|, |maxL (x ∷ (x' ∷ xs)) _| reduces to |max x (maxL (x' ∷ xs) _)|.
So using |max-≤₂|, and |≤-trans| to put things together, we finish the proof:
\restorecolumns
\begin{code}
max-greatest  (x ∷ (x' ∷ xs))    (s≤s z≤n)  (fsuc i)    =  ≤-trans 
                                                           (max-greatest _ _ i)
                                                           (max-≤₂ {x})
\end{code}
We put the whole proof in Figure \ref{Intro-proof-figure}.
\begin{figure}
%include Proof.lagda
\caption{Proof that the |max| function finds an element greater than every element in the list. \label{Intro-proof-figure}}
\end{figure}
%To end this example, we note that proving even simple (obvious) propositions in Agda takes quite a bit of work, and a lot of code, but generally not much thinking. After this extended example, we feel that we have illustrated most of the techniques that will be used later on in the report. As we wrote in the introduction to the section, we will often only give the types of the propositions, followed with the types of important lemmas and note what part of the arguments we pattern match on and in what order.

%We also feel that we have illustrated the fact that proving something in Agda often requires a lot of code, but not much thinking, as the above proof essentially proceeds as one would intuitively think to prove the specification correct. Most of the standard concepts used are available in one form or another from the standard library, and we have attempted to keep our names consistent with it (the actual code given in later sections uses the standard library when possible, but we try to include simplified definitions in this report).
\subsection{Final remarks about Agda}
We end the section about Agda by going over a few parts of Agda that we have not mentioned but will be used in the remainder of the report. 

First, Agda has Standard Library that contains most of the definitions we have made above (sometimes under slightly different names, for example, |_∧_| is called |_×_|, and in more generality---definitions are made to work for all of |Set₁|, |Set₂|, \ldots). In the remainder of the report, and in our library proving the correctness of Valiant's algorithm, we use the Standard Library definitions whenever possible.

Our second comment is about the structure of Agda programs. Agda code is partitioned into modules, which contain a sequence of function and datatype definitions. 
Modules can be imported, and an imported module can be opened to bring all definitions into scope in the current module. Additionally, modules can be parametrised by elements of a datatype, which basically means that all functions in the module take an extra argument of that type. To open a parametrised module, an element of the parameter type is needed. We use parametrised modules frequently in this report and in our library, starting in Section \ref{Matrices}.

Finally, there is another way to define a datatype: as a record. A record is similar to a product type, but each field is given a name. This is useful when there is a lot of fields and there is no natural ordering of them. Records behave like small modules, they can contain function definitions, and they can be parametrised and opened, like modules, bringing all their fields and definitions into scope. As an example, we define a record type of a pair:
\begin{code}
record Pair (A B : Set) : Set where
  field
    fst : A
    snd : B
\end{code}
When defining algebraic structures in Section \ref{Algebra}, records are very useful for handling the axioms needed, since they have no natural ordering.
