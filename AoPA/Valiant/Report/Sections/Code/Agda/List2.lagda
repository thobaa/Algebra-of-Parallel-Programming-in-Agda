%if False
\begin{code}
open import Agda.List1
open import Agda.CH
module Agda.List2 where

infix 4 _≡_
\end{code}
%endif
We now go back to defining the |maxL| function. First, for convenience, we define a strictly less than relation:
\begin{code}
_<_ : ℕ → ℕ → Set
m < n = suc m ≤ n
\end{code}
We do not need to create a new datatype using |data| for this since we can use the fact that |m < n| should be equivalent to |suc m ≤ n|. In fact, with this definition, Agda will replace any occurence of |m < n| by |suc m ≤ n| internally, which helps us when we write proofs. 

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
On the first line, we use the absurd pattern |()| to denote the empty case resulting from pattern matching on the proof (there are no cases when pattern matchin on an element of |1 ≤ 0|, and |()| is used to denote this, since Agda does not allow us to just leave out a case). On the second two lines, we don't care about what the input proof is (it is |s≤s z≤n| in both cases, so we write |_|, which takes the place of the variable but doesn't allow it to be used in the definition to signify that it's not important).

We also need an indexing function (to specify that |maxL xs _| is in the list), and again, we only define it for sensible inputs (nonempty lists). The simplest definition would probably be:
\begin{code}
index : ∀ {a} → (xs : [ a ]) → (n : ℕ) → (n < length xs) → a
index [] n ()
index (x ∷ xs) zero _ = x
index (x ∷ xs) (suc n) (s≤s m≤n) = index xs n m≤n
\end{code}
Where we needed the proof in the last line, to call the |index| function recursively.\todo{ALL: revised to about here}

However, the above definition leads to a bit of trouble later on when we want to specify things about |maxL|. In particular when we want to say that the maximum is in the list. We want to say that there is an index $n$ such that the $n$th element of the list is equal to the maximum. But to say this, we'd need to prove that $n$ was less than the length of the list. One attempt to do this is with the proposition |(n≤|xs| : n ≤ length xs) → index xs n n≤|xs| ≡ maxL xs 0<|xs||, but this is wrong, since this proposition states that \emph{if} there is a proof that |n ≤ length xs|, then we need to have that all |n > length xs| satisfy |P|, and this is clearly not what we want. The simplest way to fix this is to state that we want an integer that is |n| less than |length xs| and that the |n|th element of |xs| is equal to the max. However, there is a problem here too. To be able to index into the |n|th position, we need the proof that |n ≤ length xs|, so we can't use a pair (because the second element would have to depend on the first \todo{expand on this, and clean up: curry howard says some things, can move away from it, or state that there is a pair, but the existence must be on the left of the implication}. 

Instead, we choose to define datatype |Fin n| containing the numbers less than |n|, and change the |index| function to use it instead of |ℕ|:
\begin{code}
data Fin : (n : ℕ) → Set where
  fzero : {n : ℕ} → Fin (suc n)
  fsuc  : {n : ℕ} → (i : Fin n) → Fin (suc n)
\end{code}
That is, |f0| (representing |0|, but given a different name for clarity---it is not equal to the natural number |0|, they don't even have the same type) is less than any number greater than or equal to |1|, and for any number |i|, less than some number |n|, |fsuc i| is less than |n + 1|. 
Note that we have put the index |n| on the right side of the colon n the definition of |Fin|, this is so that [todo: is there a reason??? something with it being indexed (doesn't work if we move it).
Alternatively, we could define |Fin n| as a dependent pair of a natural number |i| and a proof that it is less than |n|. For future use, we define a dependent pair type first (we could of course have used it to define the regular pair for the Curry Howard Correspondence): 
\begin{code}
data Σ (A : Set) (B : A → Set) : Set where
  _,_ : (x : A) → B x → Σ A B 
\end{code}
Here, on the other hand, we need to put the arguments to |Σ| on the left hand side of the colon, because otherwise the type would be too big [todo : Huh?]
And then use it to define |Fin′|.
\begin{code}
Fin′ : (n : ℕ) → Set
Fin′ n = Σ ℕ (λ i → i < n)
\end{code}
This second representation has the advantage that the natural number is close by (|i| is an actual natural number, that we can use right away, for the other |Fin| type, we would have to write and use a translation-function that replaces each |fsuc| by |suc| and |fzero| by |zero|).

However, this would require us to always extract the proof when we need to use it, instead of having it ``built into'' the type.
These two different ways of defining things are something we will use later when we define upper triangular matrixes as their own data-type. For a concrete representation, we are going to use the first kind of representation, where we have built in the ``proof'' that the matrix is triangular---which lets us not worry about modifying the proof appropriately, or reprove that the product of two upper triangular matrixes is again upper triangular. While when representing matrixes abstractly (as functions from their indices), we will need to use the proofs and modify them, to strengthen some results from the concrete case.

We now redefine the indexing function, with different syntax, more familiar to Haskell users (and see already that not needing a separate proof argument makes things a lot clearer)
\begin{code}
infix 10 _‼_
_‼_ : ∀ {a} → (xs : [ a ]) → (n : Fin (length xs)) → a
[] ‼ ()
(x ∷ xs) ‼ fzero = x
(x ∷ xs) ‼ fsuc i = xs ‼ i
\end{code}
The final step is defining equality, i.e., the proposition that two values |x| and |y| are equal. The basic equality is a data type whose only constructor |refl| is a proof that |x| is equal to itself.
\begin{code}
data _≡_ {a : Set} : a → a → Set where
  refl : {x : a} → x ≡ x
\end{code}
For our purposes, this very strong concept of equality is suitable (it is the smallest relation satisfying |x ≡ x|). However, if one wants to allow different ``representations'' of an object, for example if one defines the rational numbers as pairs of integers, |ℚ = ℤ × ℤ\{0}|, one wants a concept of equality that considers |(p , q)| and |(m * p , m * q)| to be  equal. This could be taken care of by using equality defined as for example [TODO: what about division by $0$]

Another example is if we define a datatype of sets, we want two sets to be equal as long as they have the same elements, regardless if they were added in different orders, or if one set had the same element added multiple times.


Now we can finally express our specification in Agda.
\begin{code}
max-spec : (xs : [ ℕ ]) → (pf : 0 < length xs) → 
         ((n : Fin (length xs)) → xs ‼ n ≤ maxL xs pf) 
           ∧
         ∃ (λ n → xs ‼ n ≡ maxL xs pf)
\end{code}
To prove the correctness of the |max| function, we must then find an implementation of |max-spec|, that is, we produce an element of its type, corresponding to a proof of the proposition it represents.This is actually quite a substantial task, that we accomplish in the following two sections. In Section \ref{extended-example-first-part-of-proof} we prove the first part of the disjunct, and in Section \ref{extended-example-second-part-of-proof}, we prove the second.

\subsection{First part of proof}
\label{extended-example-first-part-of-proof}
This is actually quite a substantial task. We begin by proving the first disjunct |(n : Fin (length xs)) → xs ‼ n ≤ maxL xs pf| 
\begin{code}
max-greatest : {xs : [ ℕ ]} → {pf : 0 < length xs} → 
         (n : Fin (length xs)) → xs ‼ n ≤ maxL xs pf
\end{code}
We have made the list and the proof that the length is greater than $0$ implicit arguments because they can be infered from the resulting type |xs ‼ n ≤ maxL xs pf|. However, when we prove the lemma, we are going to need to pattern match on those arguments many times.

We make the simple, but important observation that we cannot use |max-greatest| in the place of |(n : Fin (length xs)) → xs ‼ n ≤ maxL xs pf| when giving the type of |max-spec|, because while the type of |max-greatest| is the proposition that |maxL xs pf| is the greatest element of the list, |max-greatest| itself is just one specific proof of that proposition.
\todo{is |max-greatest| a good name for it?}

%The overall strategy for proving things in Agda is to begin by writing the implementation with holes, in this case:
%\begin{spec}
%max-greatest = {! !}
%\end{spec}
%Then we look at the structure of what is to be proved. 
%Then we begin by writing the arguments  
To prove a proposition in Agda, it is important to look at the structure of the proposition, and the structures of the involved parts. Then one needs to determine which structure should be pattern matched on, depending on what the inductive step in the proposition is.

To prove |max-greatest|, we begin by formulating the proof informally. The main idea we use is pattern matching the index into the list, if it is $0$, we want to prove the simpler proposition that |x ≤ maxL (x ∷ xs) pf|, which we call |max-greatest-initial|, because it is essentially the initial step in an induction on the index:
\begin{code}
max-greatest-initial : {x : ℕ} {xs : [ ℕ ]} → x ≤ maxL (x ∷ xs) (s≤s z≤n)
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

Using |max-increasing₁| and |≤-refl|, we are able to prove the initial step in the induction proof, |max-greatest-initial|. We pattern match on the remainter of the list, if it is |[]|, we need to show that |x ≤ x|, which is done with |≤-refl|, and if it is |x′ ∷ xs|, we need to prove that |x ≤ maxL (x ∷ (x′ ∷ xs)) pf|, and expanding this using the definition of |max|, we find that we need to prove that |x ≤ max x (maxL (x′ ∷ xs) pf′)|, which is exactly what |max-increasing₁| does.
\begin{code}
max-greatest-initial {x} {[]} = ≤-refl
max-greatest-initial {x} {x′ ∷ xs} = max-increasing₁
\end{code}
Finally, we are able to finish our proof of |max-greatest|. As we said above, we want to pattern match on the index, however, this is not possible to do right away, since the available constructors (if any) for |Fin (length xs)| depends on the length of |xs|. Therefore, we begin by pattern matching on the list. If the list is empty, we fill in the absurd pattern |()| for the proof that it is nonempty. Otherwise, we pattern match on the index. 
If the index is |fzero|, we use the initial step |max-greatest-initial|, to prove that |x ≤ maxL (x ∷ xs) pf|. 
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
max-greatest {[]} {()} _
max-greatest {x ∷ xs} {s≤s z≤n} fzero = max-greatest-initial {x} {xs}
max-greatest {x ∷ []} {s≤s z≤n} (fsuc ())
max-greatest {x ∷ (x′ ∷ xs)} {s≤s z≤n} (fsuc i) = ≤-trans (max-greatest i) (max-increasing₂ {x})
\end{code}

\subsection{Second part of proof}
\label{extended-example-second-part-of-proof}
\todo{Make first part of proof, making of specification, etc subsections (or something)}
In this section, we will prove the disjunction in the specification, that is: \todo{Is |pf| a good name for a proof, or should they be more descriptive?}
\begin{code}
max-in-list : {xs : [ ℕ ]} → {pf : 0 < length xs} → 
         ∃ (λ n → xs ‼ n ≡ maxL xs pf)
\end{code}
This is a bit different from the previous proof, because the definition of the existential quantifier |∃| in constructive mathematics states that we actually need a function that finds the maximum in the list and remembers that it is the maximum. So proving that something exists is in mainly a programming problem---in particular 

To find a function that does this, we begin by getting rid of the case when the list is empty, since then, there is no proof that it is non-empty. Then we look at the definition of |max|. If the list contains only one element, we can return |(fzero, refl)|, since the first element is returned by |max| and also by indexing at |fzero|, and |refl| proves that an element is equal to itself. That was the base case. If the list has at least two elements, we can find the maximum in the remaining list by induction. Depending on whether the first element is greater than this maximum or not, we then either return |(fzero , refl)| again, or increase the returned value and modify the proof returned by the maximum function.

The fact that we need the proof means that we can't simply define a type |Bool| and an if statement:
%if False
\begin{code}
data Bool : Set where
  True  : Bool
  False : Bool
data bool : Set where
  true  : bool
  False : bool
not : Bool → Bool
not True = False
not False = True
\end{code}
\begin{code}
if_then_else : {a : Set} → Bool → a → a → a
if True  then x else y = x
if False then x else y = y
\end{code}
%endif
Along with a check like (we use the prime because we want the similar function we will actually use to be named |_≤?_|):
\begin{code}
_≤?′_ : ℕ → ℕ → Bool
_≤?′_ zero n = False
_≤?′_ (suc m) zero = True
_≤?′_ (suc m) (suc n) = m ≤?′ n
\end{code}
Because while |if (x ≤?′ y) then x else y| does return the maximum, it doesn't return a proof, and we cannot use it to convince Agda that |x ≤ y| or vice versa.
Instead, we need a function like that along with a |Bool|-like answer returns a proof that it is correct. This is exactly the point of the data type |Dec| we defined above \ref{decidable-def}.

So we want define the function |_≤?_| to return |yes x≤y|, where |x≤y : x ≤ y| is a proof that |x| is less than or equal to |y|, or |no ¬x≤y|, where |¬x≤y : ¬ (x ≤ y)|. If |x == 0|, this is straightforward, since we simply return |yes z≤n|. If |x == suc x′|, we need to pattern match on |y|. The simples case is if |y == 0|, because then we need to derive |⊥| from |suc x′ ≤ 0|. 
%Since, |s≤s z≤n| is a proof that |0 < suc x′|, we define a lemma |x<y⇒¬y≤x| that states that if |x < y|, then |¬ (y ≤ x)|. Since |x < y| expands to |suc x ≤ y|, and hence, |y == suc y′|, and the proof of |x < y| must be |s≤s x<y′|. 
\todo{More here (think about what the proof does, really) Also write that we curry/uncurry--whatever, actually ,this might be unneccessary}
%begin{code}
%--x<y⇒¬y≤x : {x y : ℕ} → (x < y) → ¬ (y ≤ x)
%--x<y⇒¬y≤x (s≤s x<y′) y′<x = x<y⇒¬y≤x y′<x x<y′
%end{code}
%Using this, we can hence finish the case |x == suc x′| and |y == 0|. 

Next, in the case where |x == suc x′| and |y == suc y′|, we need to know (with proof) which of |x′| and |y′| is greater. We need to pattern match on the |Dec (x′ ≤ y′)|, which is not part of the function arguments, and do this by introducing a new piece of Agda syntax, the |with| statement (we could of course use a helper function to do the pattern matching, but the with statement is simpler). After the function arguments, one writes |with| followed by a list of expressions to pattern match on, separated by vertical bars:| || |. Then on the line below, one writes either |...| in place of the old arguments, followed by a bar, | || |, and the new arguments separated by bars, or (in case one wants to infer things about the old arguments based on the pattern matching), one repeats the function arguments in place of the |...|. We show both alternatives.
\begin{code}
_≤?_ : (x y : ℕ) → Dec (x ≤ y) 
zero  ≤? n = yes z≤n
suc m ≤? zero = no (λ ()) --(x<y⇒¬y≤x (s≤s z≤n))
suc m ≤? suc n with m ≤? n 
...            | yes m≤n = yes (s≤s m≤n)
suc m ≤? suc n | no  n≤m = no (λ x → n≤m (p≤p x))
  where p≤p : {m n : ℕ} → (suc m ≤ suc n) → m ≤ n
        p≤p (s≤s m≤n) = m≤n
\end{code}
Above, we made a local definition of the proposition |p≤p| stating that if both |m| and |n| are the successors of something, and if |m ≤ n|, then the predecessor of |m| is less than or equal to the predecessor of |n|.

We note that in the above example, we didn't actually need to use the |with| construction, since we didn't use the result of the pattern matching (if we had pattern matched on |m≤n| above, we could have inferred that whether the argument |m| to |suc m| was |zero| or |suc m'|, but that wasn't neccessary for this proof \todo{include ref to where it is actually neccessary (if ever in this report)}). We could instead have introduced a helper function (perhaps locally) that we call in place of the with statement:
\begin{spec}
helper : {m n : ℕ} → Dec (m ≤ n) → Dec ((suc m) ≤ (suc n))
helper (yes p) = yes (s≤s p)
helper (no ¬p) = no (λ x → ¬p (p≤p x))
\end{spec}
So we write
\begin{spec}
min-finder x (x′ ∷ xs) with x ≤? max (x′ ∷ xs) _
\end{spec}

Now, we begin with the the case where |x ≤? max| returns |yes x≤max|. We thus have a proof that |x ≤ max (x′ ∷ xs)|, and by recursively calling |min-finder x′ xs| \todo{make sure I mention |min-finder| name when introducing it above}, we get an index |i| and a proof that the |i|th element of |x′ ∷ xs| is the greatest element there. Hence, the index of our maximum should be |fsuc i|, and we need to prove that given the above, |max (x ∷ x′ ∷ xs) ≡ max (x′ ∷ xs)|, since then, the |fsuc i|th element in |x ∷ x′ ∷ xs| would be equal to |max (x′ ∷ xs)| by the definition of |‼|, and hence to |max (x ∷ x′ ∷ xs)|.. We introduce the function |move-right| to move the proof one step to the right.
\begin{code}
move-right : {x x′ : ℕ} {xs : [ ℕ ]} → x ≤ maxL (x′ ∷ xs) (s≤s z≤n) → ∃ (λ i → (x′ ∷ xs) ‼ i ≡ maxL (x′ ∷ xs) (s≤s z≤n)) → ∃ (λ i → (x ∷ x′ ∷ xs) ‼ i ≡ max x (maxL (x′ ∷ xs) (s≤s z≤n)))
\end{code}
We write out the arguments as 
\begin{spec}

\end{spec}
pattern match on the existence proof, getting |(i , pf)|. We already know that the first part of the pair |move-right| should return (the witness) should be |fsuc i|, 
\begin{code}
-- No CASE
≡-cong : {a b : Set} {x y : a} → (f : a → b) → x ≡ y → f x ≡ f y
≡-cong f refl = refl

≡-trans : ∀ {a b c} → a ≡ b → b ≡ c → a ≡ c
≡-trans refl refl = refl

x≡maxx0 : {x : ℕ} → x ≡ max x 0
x≡maxx0 {zero} = refl
x≡maxx0 {suc n} = refl

l″ : ∀ {x y} → y ≤ x → x ≡ max x y 
l″ {x} {zero} z≤n = x≡maxx0
l″ (s≤s m≤n) = ≡-cong suc (l″ m≤n)

¬x≤y⇒y≤x : {x y : ℕ} → ¬ (x ≤ y) → (y ≤ x)
¬x≤y⇒y≤x {x} {zero} pf = z≤n
¬x≤y⇒y≤x {zero} {suc n} pf with pf z≤n 
...| ()
¬x≤y⇒y≤x {suc m} {suc n} pf = s≤s (¬x≤y⇒y≤x (λ x → pf (s≤s x)))

x-maxL : (x : ℕ) (xs : [ ℕ ]) (pf : 0 < length xs) → maxL xs pf ≤ x → x ≡ maxL (x ∷ xs) (s≤s z≤n)
x-maxL x [] pf pf′ = refl
x-maxL x (x′ ∷ xs) (s≤s z≤n) pf′ = l″ pf′

-- yes case
max-is-max : (x y : ℕ) → x ≤ y → y ≡ max x y
max-is-max zero y pf = refl
max-is-max (suc m) zero () 
max-is-max (suc m) (suc n) (s≤s m≤n) = ≡-cong suc (max-is-max m n m≤n)

small-x⇒maxL-equal : (x x′ : ℕ) (xs : [ ℕ ]) → x ≤ maxL (x′ ∷ xs) (s≤s z≤n) → maxL (x′ ∷ xs) (s≤s z≤n) ≡ maxL (x ∷ x′ ∷ xs) (s≤s z≤n)
small-x⇒maxL-equal zero x′ xs pf = refl
small-x⇒maxL-equal (suc n) x′ xs pf = max-is-max (suc n) (maxL (x′ ∷ xs) (s≤s z≤n)) pf

move-right {x} {x′} {xs} x≤maxL (i , pf) = fsuc i , ≡-trans pf (small-x⇒maxL-equal x x′ xs x≤maxL)

min-finder : (x : ℕ) → (xs : [ ℕ ]) → ∃ (λ i → (x ∷ xs) ‼ i ≡ maxL (x ∷ xs) (s≤s z≤n))
min-finder x [] = fzero , refl
min-finder x (x′ ∷ xs) with x ≤? maxL (x′ ∷ xs) _
min-finder x (x′ ∷ xs) | yes x≤maxL = move-right x≤maxL (min-finder x′ xs)
min-finder x (x′ ∷ xs) | no max≤x = fzero , x-maxL x (x′ ∷ xs) _ (¬x≤y⇒y≤x max≤x)

max-in-list {[]} {()}
max-in-list {(x ∷ xs)} {s≤s z≤n} = min-finder x xs
\end{code}
\todo{note that |min″| wouldn't work, because Agda can't see that the structure gets smaller (could reformulate this wrt |max-in-list|, give different implementation}
\todo{|≤-trans| repeatedly leads to introduction of equational syntax, trap is trying to expand variables too many times}










\subsection{Finish}
Now, we are able to finish our proof of the specification by putting together the parts of the two previous sections. 

If the list is empty, the proof would be an element of |1 ≤ 0|, and that type is empty, so we can put in the absurd patern |()|. On the other hand, if the list is |x ∷ xs|, we make a pair of the above proofs, and are done:
\begin{code}
max-spec [] ()
max-spec (x ∷ xs) (s≤s z≤n) = max-greatest , max-in-list
\end{code}

To end this example, we note that proving even simple (obvious) propositions in Agda takes quite a bit of work, and a lot of code, but generally not much thinking. After this extended example, we feel that we have illustrated most of the techniques that will be used later on in the report. As we wrote in the introduction to the section, we will often only give the types of the propositions, followed with the types of important lemmas and note what part of the arguments we pattern match on and in what order.

We also feel that we have illustrated the fact that proving something in Agda often requires a lot of code, but not much thinking, as the above proof essentially proceeds as one would intuitively think to prove the specification correct. Most of the standard concepts used are available in one form or another from the standard library, and we have attempted to keep our names consistent with it (the actual code given in later sections uses the standard library when possible, but we try to include simplified definitions in this report).


\todo{fix references below (only visible in source)}
\label{decidable-def}
