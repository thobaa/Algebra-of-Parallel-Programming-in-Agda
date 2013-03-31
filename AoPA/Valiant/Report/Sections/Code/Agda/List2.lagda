%if False
\begin{code}
open import List1
open import CH
module List2 where
\end{code}
%endif
As an example, we will define a maximum function |max| for lists of natural numbers and prove that it satisfies a sensible specification. The specification we will use is that, |max xs| is greater than or equal to each element of |xs|, and equal to some element. 
First, we define the |maxℕ| function on |ℕ|.
\begin{code}
maxℕ : ℕ → ℕ → ℕ
maxℕ zero n = n
maxℕ n zero = n
maxℕ (suc m) (suc n) = suc (maxℕ m n)
\end{code}

We decide to only define the |max| function on nonempty lists (in the case of natural numbers, it might be sensible to define |max [] = 0|, but when it comes to other types, and orders, there is no least element).
 Second, we need to define less than, |_≤_|. This is done with the following data type: 
\begin{code}
infix 3 _≤_
data _≤_ : ℕ → ℕ → Set where
  z≤n : {n : ℕ} → zero ≤ n
  s≤s : {m n : ℕ} → (m≤n : m ≤ n) → suc m ≤ suc n 
\end{code}
Here we introduce another feature of Agda, that functions can take implicit arguments, the constructor |z≤n| takes an argument |n|, but Agda can figure out what it is from the resulting type (which includes |n|), and hence, we don't need to include it.

Viewed through the Curry Howard Correspondence, the data type |m ≤ n| represents the proposition that |m| is less than or equal to |n|, and the two possible proofs of this are, either |m| is |zero|, which is less than any natural number, or |m = suc m′| and |n = suc n′| and we have a proof of |m′ ≤ n′|.
Using the above definition, we can also define a less than function, 
\begin{code}
_<_ : ℕ → ℕ → Set
m < n = suc m ≤ n
\end{code}
We note that we didn't need to create a new type using the |data| command to create this, 

Now we define the |length| function for lists, 
\begin{code}
length : {a : Set} → [ a ] → ℕ
length [] = 0
length (x ∷ xs) = suc (length xs)
\end{code}
Now, we can define the |max| function:
\begin{code}
max : (xs : [ ℕ ]) → (0 < length xs) → ℕ
max [] ()
max (x ∷ []) _ = x
max (x ∷ (x′ ∷ xs)) _ = maxℕ x (max (x′ ∷ xs) (s≤s z≤n))
\end{code}
On the first line, we use the absurd pattern |()| \todo{Explain why () can be used} to show that there is no proof that |1 ≤ 0|. On the second two lines, we don't care about what the input proof is (it is |s≤s z≤n| in both cases, so we use |_| to signify that it's not important). \todo{NAmes of |_|-pattern -- if there is one}

We also need an indexing function, and again, we can only define it for sensible inputs. The simplest definition would probably be:
\begin{code}
index : ∀ {a} → (xs : [ a ]) → (n : ℕ) → suc n ≤ length xs → a
index [] n ()
index (x ∷ xs) zero _ = x
index (x ∷ xs) (suc n) (s≤s m≤n) = index xs n m≤n
\end{code}
However, this leads to a bit of trouble later on, when we want to specify things about it, in particular when we want to say that the maximum is in the list. We want to say that there is an index $n$ such that the $n$th element of the list is equal to the maximum. But to say this, we'd need to prove that the $n$ was less than the length of the list, and the simple way to do this would be to attempt to use the proposition |P = (proof : n ≤ length xs) → index xs n proof ≡ max xs lengthproof|, but this is horribly wrong, because it states something completely different to what we want. It states that if there is a proof that |n ≤ length xs|, then we need to have that all |n > length xs| satisfy |P|, and this is clearly not what we want. The simplest way to fix this is to state that we want an integer that is |n| less than |length xs| and that the |n|th element of |xs| is equal to the max. However, there is a problem here too. To be able to index into the |n|th position, we need the proof that |n ≤ length xs|, so we can't use a pair (because the second element would have to depend on the first \todo{expand on this, and clean up: curry howard says some things, can move away from it, or state that there is a pair, but the existence must be on the left of the implication}. Instead, we choose to define datatype |Fin n| containing the numbers less than |n|, and change the |index| function to use it instead of |ℕ|:
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
This second representation has the advantage that the natural number is close by (|i| is an actual natural number, that we can use right away, for the other |Fin| type, we would have to write and use a translation-function that replaces each |fsuc| by |suc| and |fzero| by |zero|) .

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
infix 3 _≡_
data _≡_ {a : Set} : a → a → Set where
  refl : {x : a} → x ≡ x
\end{code}
Here, we have an implicit argument to the \emph{type}, to allow it to work for an type. For our purposes, this very strong concept of equality is suitable. However, if one wants to allow different ``representations'' of an object, for example if one defines the rational numbers as pairs of integers, |ℚ = ℤ × ℤ\{0}|, one wants a concept of equality that considers |(p , q)| and |(m * p , m * q)| to be  equal. This could be taken care of by using equality defined as for example [TODO: what about division by $0$]
%if False
\begin{code}
infixl 2 _*_
infixl 2 _*′_
postulate
  ℤ   : Set
  ℤ\0 : Set
  _*′_ : ℤ\0 → ℤ\0 → ℤ\0
  _*_ : ℤ\0 → ℤ → ℤ
ℚ : Set
ℚ = ℤ ∧ ℤ\0
\end{code}
%endif
\begin{code}
data _≡′_ : ℚ → ℚ → Set where
  p/q≡mp/mq : {p : ℤ}{q : ℤ\0} (m : ℤ\0) → (p , q) ≡′ (m * p , m *′ q)
\end{code}
Another example is if we define a datatype of sets, we want two sets to be equal as long as they have the same elements, regardless if they were added in different orders, or if one set had the same element added multiple times.


Now we can finally express our specification in Agda.
\begin{code}
max-spec : (xs : [ ℕ ]) → (pf : 0 < length xs) → 
         ((n : Fin (length xs)) → xs ‼ n ≤ max xs pf) 
           ∧
         ∃ (λ n → xs ‼ n ≡ max xs pf)
\end{code}
To prove the correctness of the |max| function, we must then find an implementation of |max-spec|, that is, we produce an element of its type, corresponding to a proof of the proposition it represents.This is actually quite a substantial task, that we accomplish in the following two sections. In Section \ref{extended-example-first-part-of-proof} we prove the first part of the disjunct, and in Section \ref{extended-example-second-part-of-proof}, we prove the second.

\subsection{First part of proof}
\label{extended-example-first-part-of-proof}
This is actually quite a substantial task. We begin by proving the first disjunct |(n : Fin (length xs)) → xs ‼ n ≤ max xs pf| 
\begin{code}
max-greatest : {xs : [ ℕ ]} → {pf : 0 < length xs} → 
         (n : Fin (length xs)) → xs ‼ n ≤ max xs pf
\end{code}
We have made the list and the proof that the length is greater than $0$ implicit arguments because they can be infered from the resulting type |xs ‼ n ≤ max xs pf|. However, when we prove the lemma, we are going to need to pattern match on those arguments many times.

We make the simple, but important observation that we cannot use |max-greatest| in the place of |(n : Fin (length xs)) → xs ‼ n ≤ max xs pf| when giving the type of |max-spec|, because while the type of |max-greatest| is the proposition that |max xs pf| is the greatest element of the list, |max-greatest| itself is just one specific proof of that proposition.
\todo{is |max-greatest| a good name for it?}

%The overall strategy for proving things in Agda is to begin by writing the implementation with holes, in this case:
%\begin{spec}
%max-greatest = {! !}
%\end{spec}
%Then we look at the structure of what is to be proved. 
%Then we begin by writing the arguments  
To prove a proposition in Agda, it is important to look at the structure of the proposition, and the structures of the involved parts. Then one needs to determine which structure should be pattern matched on, depending on what the inductive step in the proposition is.

To prove |max-greatest|, we begin by formulating the proof informally. The main idea we use is pattern matching the index into the list, if it is $0$, we want to prove the simpler proposition that |x ≤ max (x ∷ xs) pf|, which we call |max-greatest-initial|, because it is essentially the initial step in an induction on the index:
\begin{code}
max-greatest-initial : {x : ℕ} {xs : [ ℕ ]} → x ≤ max (x ∷ xs) (s≤s z≤n)
\end{code}
On the other hand, if the index is $i + 1$, we must have that the list must has length at least $2$, we proceed by doing noting:
\begin{enumerate}
\item \label{Ex.List.Induction1} By induction, the $i$th element of the tail is less than the greatest element of the tail.
\item \label{Ex.List.Induction2} The $i$th element of the tail equals the $i + 1$th element of the list.
\item \label{Ex.List.Induction3} By the definition of |max|, |max (x ∷ (x′ ∷ xs)) pf| expands to |maxℕ x (max (x′ ∷ xs) pf′)|, and for any |x| and |y|, we have |y ≤ maxℕ x y|.
\end{enumerate}
To translate the induction case into Agda code, we need to introduce two new lemmas. By induction, we already know that Point \ref{Ex.List.Induction1} is true. Additionally, Agda infers Point \ref{Ex.List.Induction2}. However, we still need to prove the second part of Point \ref{Ex.List.Induction3}:
\begin{code}
maxℕ-increasing₂ : {m n : ℕ} → n ≤ maxℕ m n
\end{code}
Where the subscript $2$ refers to the fact that it is the second argument of |maxℕ| that is on the left hand side of the inequality. Finally, we need a way to piece together inequalities, if |i ≤ j| and |j ≤ k|, then |i ≤ k| (that is, |≤| is transitive):
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

We continue by proving |maxℕ-increasing₂|, for this, we introduce a lemma: |≤-refl|, stating that for any |n|, |n ≤ n| (that is, |≤| is reflexive), which is very easy to prove (if |n == 0|, a proof is given by the constructor |z≤n|, and if |n == suc n′|, by induction, |n′ ≤ n′| and |s≤s| takes the proof of this to a proof that |n ≤ n|:
\begin{code}
≤-refl : {n : ℕ} → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl
\end{code}
Now we prove |maxℕ-increasing₂|.
%if False
\begin{code}
maxℕ-increasing₁ : {m n : ℕ} → m ≤ maxℕ m n
maxℕ-increasing₁ {zero} {y} = z≤n
maxℕ-increasing₁ {suc n} {zero} = ≤-refl
maxℕ-increasing₁ {suc n} {suc n′} = s≤s maxℕ-increasing₁
\end{code}
%endif
We do this by pattern matching on the second argument (because it is the one involved in the inequality, and depending on its value, we need different constructors for the inequality proof). If it is |zero|, we use the constructor |z≤n|, regardless of what the first argument is. If it is |suc n′|, we need to know what the first argument was, so we pattern match on it. If the first argument is |zero|, then, from the definition of |maxℕ|, we know that |maxℕ zero (suc n′) == suc n′|, so we want to prove that |suc n′ ≤ suc n′|, which we do by using the lemma |≤-refl| (we note here that we didn't actually need the fact that the second argument was non-zero). On the other hand, if the first argument is |suc m′|, we know by induction (we call |maxℕ-increasing₂| where we need to supply at least the first argument, since it doesn't appear anywhere, and hence Agda is unable to infer it) that |n′ ≤ maxℕ m′ n′|, so we use |s≤s| to get |suc n′ ≤ suc (maxℕ m′ n′)|, and from the definition of |maxℕ|, we (and more importantly Agda) get that |suc (maxℕ m′ n′) == maxℕ (suc m′) (suc n′)|, so we are in fact done.
\begin{code}
maxℕ-increasing₂ {m} {zero} = z≤n
maxℕ-increasing₂ {zero} {suc n′} = ≤-refl
maxℕ-increasing₂ {suc m′} {suc n′} = s≤s (maxℕ-increasing₂ {m′} {n′})
\end{code}
We also prove the similar proposition, |maxℕ-increasing₁ : {m n : ℕ} → m ≤ maxℕ m n|, that |maxℕ| is greater than its first argument, in essentially the same way (we pattern match first on the first argument instead).\todo{check that variable names are reasonably consistent}

Using |maxℕ-increasing₁| and |≤-refl|, we are able to prove the initial step in the induction proof, |max-greatest-initial|. We pattern match on the remainter of the list, if it is |[]|, we need to show that |x ≤ x|, which is done with |≤-refl|, and if it is |x′ ∷ xs|, we need to prove that |x ≤ max (x ∷ (x′ ∷ xs)) pf|, and expanding this using the definition of |max|, we find that we need to prove that |x ≤ maxℕ x (max (x′ ∷ xs) pf′)|, which is exactly what |maxℕ-increasing₁| does.
\begin{code}
max-greatest-initial {x} {[]} = ≤-refl
max-greatest-initial {x} {x′ ∷ xs} = maxℕ-increasing₁
\end{code}
Finally, we are able to finish our proof of |max-greatest|. As we said above, we want to pattern match on the index, however, this is not possible to do right away, since the available constructors (if any) for |Fin (length xs)| depends on the length of |xs|. Therefore, we begin by pattern matching on the list. If the list is empty, we fill in the absurd pattern |()| for the proof that it is nonempty. Otherwise, we pattern match on the index. 
If the index is |fzero|, we use the initial step |max-greatest-initial|, to prove that |x ≤ max (x ∷ xs) pf|. 
If the index is |fsuc i|, we pattern match on the tail of the list. If it is empty, we know that the index shouldn't have been |fsuc i|, because we'd have |i : Fin zero|, so we fill in |i| with the absurd pattern |()|.
The case we have left is when the list is |x ∷ (x′ ∷ xs)|, and the index is |fsuc i|. As we said above, we use induction to prove that |(x′ ∷ xs) ‼ i ≤ max (x′ ∷ xs) pf|. By the definition of |‼|, we have that
\begin{spec}
(x ∷ (x′ ∷ xs)) ‼ (fsuc i) == (x′ ∷ xs) ‼ i
\end{spec}
So by induction, |max-greatest i| proves that |(x ∷ (x′ ∷ xs)) ‼ (fsuc i) ≤ max (x′ ∷ xs) pf|, and additionally, from the definition of |max|, 
\begin{spec}
max (x ∷ (x′ ∷ xs)) pf == maxℕ x (max (x′ ∷ xs) pf′)
\end{spec}
So using |maxℕ-increasing₂|, and |≤-trans| to put things together, we get \todo{clean up the proofs ``pf'' that are input to max} the desired result:
\begin{code}
max-greatest {[]} {()} _
max-greatest {x ∷ xs} {s≤s z≤n} fzero = max-greatest-initial {x} {xs}
max-greatest {x ∷ []} {s≤s z≤n} (fsuc ())
max-greatest {x ∷ (x′ ∷ xs)} {s≤s z≤n} (fsuc i) = ≤-trans (max-greatest i) (maxℕ-increasing₂ {x})
\end{code}

\subsection{Second part of proof}
\label{extended-example-second-part-of-proof}
\todo{Make first part of proof, making of specification, etc subsections (or something)}
In this section, we will prove the disjunction in the specification, that is: \todo{Is |pf| a good name for a proof, or should they be more descriptive?}
\begin{code}
max-in-list : {xs : [ ℕ ]} → {pf : 0 < length xs} → 
         ∃ (λ n → xs ‼ n ≡ max xs pf)
\end{code}
This is a bit different from the previous proof, because the definition of the existential quantifier |∃| in constructive mathematics states that we actually need a function that finds the maximum in the list and remembers that it is the maximum. So proving that something exists is in mainly a programming problem---in particular 

To find a function that does this, we begin by getting rid of the case when the list is empty, since then, there is no proof that it is non-empty. Then we look at the definition of |max|. If the list contains only one element, we can return |(fzero, refl)|, since the first element is returned by |max| and also by indexing at |fzero|, and |refl| proves that an element is equal to itself. That was the base case. If the list has at least two elements, we can find the maximum in the remaining list by induction. Depending on whether the first element is greater than this maximum or not, we then either return |(fzero , refl)| again, or increase the returned value and modify the proof returned by the maximum function.

The fact that we need the proof means that we can't simply define a type |Bool| and an if statement:
\begin{code}
data Bool : Set where
  True  : Bool
  False : Bool

if_then_else : {a : Set} → Bool → a → a → a
if True  then x else y = x
if False then x else y = y
\end{code}
Along with a check like (we use the prime because we want the similar function we will actually use to be named |_≤?_|):
\begin{code}
_≤?′_ : ℕ → ℕ → Bool
_≤?′_ zero n = False
_≤?′_ (suc m) zero = True
_≤?′_ (suc m) (suc n) = m ≤?′ n
\end{code}
Because while |if (x ≤?′ y) then x else y| does return the maximum, it doesn't return a proof, and we cannot use it to convince Agda that |x ≤ y| or vice versa.
Instead, we need a function like that along with a |Bool|-like answer returns a proof that it is correct. This is exactly the point of the data type |Dec| we defined above \ref{dec}.
\begin{code}
≡-cong : {a b : Set} {x y : a} → (f : a → b) → x ≡ y → f x ≡ f y
≡-cong f refl = refl

≡-trans : ∀ {a b c} → a ≡ b → b ≡ c → a ≡ c
≡-trans refl refl = refl

x≡maxℕx0 : {x : ℕ} → x ≡ maxℕ x 0
x≡maxℕx0 {zero} = refl
x≡maxℕx0 {suc n} = refl

l″ : ∀ {x y} → y ≤ x → x ≡ maxℕ x y 
l″ {x} {zero} z≤n = x≡maxℕx0
l″ (s≤s m≤n) = ≡-cong suc (l″ m≤n)

lemma : ∀ x xs pf → max xs pf ≤ x → x ≡ max (x ∷ xs) (s≤s z≤n)
lemma x [] pf pf′ = refl
lemma x (x′ ∷ xs) (s≤s z≤n) pf′ = l″ pf′

x<y⇒¬y≤x : {x y : ℕ} → (x < y) → ¬ (y ≤ x)
x<y⇒¬y≤x (s≤s m≤n) = λ x → x<y⇒¬y≤x x m≤n

¬x≤y⇒y≤x : {x y : ℕ} → ¬ (x ≤ y) → (y ≤ x)
¬x≤y⇒y≤x {x} {zero} pf = z≤n
¬x≤y⇒y≤x {zero} {suc n} pf with pf z≤n 
...| ()
¬x≤y⇒y≤x {suc m} {suc n} pf = s≤s (¬x≤y⇒y≤x (λ x → pf (s≤s x)))

p≤p : {m n : ℕ} → (suc m ≤ suc n) → m ≤ n
p≤p (s≤s m≤n) = m≤n

_≤?_ : (x : ℕ) → (y : ℕ) → Dec (x ≤ y) 
zero  ≤? n = yes z≤n
suc m ≤? zero = no (x<y⇒¬y≤x (s≤s z≤n))
suc m ≤? suc n with m ≤? n 
...| yes m≤n = yes (s≤s m≤n)
...| no n≤m = no (λ x → n≤m (p≤p x))

maxℕ-is-max : (x y : ℕ) → x ≤ y → y ≡ maxℕ x y
maxℕ-is-max zero y pf = refl
maxℕ-is-max (suc m) zero () 
maxℕ-is-max (suc m) (suc n) (s≤s m≤n) = ≡-cong suc (maxℕ-is-max m n m≤n)

lemma″ : ∀ x x′ xs → x ≤ max (x′ ∷ xs) (s≤s z≤n) → max (x′ ∷ xs) (s≤s z≤n) ≡ maxℕ x (max (x′ ∷ xs) (s≤s z≤n))
lemma″ zero x′ xs pf = refl
lemma″ (suc n) x′ xs pf = maxℕ-is-max (suc n) (max (x′ ∷ xs) (s≤s z≤n)) pf

increase : ∀ x x′ xs → x ≤ max (x′ ∷ xs) (s≤s z≤n) → ∃ (λ i → (x′ ∷ xs) ‼ i ≡ max (x′ ∷ xs) (s≤s z≤n)) → ∃ (λ i → (x ∷ x′ ∷ xs) ‼ i ≡ maxℕ x (max (x′ ∷ xs) (s≤s z≤n)))
increase x x′ xs pf′ (i , pf) = fsuc i , ≡-trans pf (lemma″ x x′ xs pf′)

-- en max funktion som tar värde och kanske tom lista

min-finder : (x : ℕ) → (xs : [ ℕ ]) → ∃ (λ i → (x ∷ xs) ‼ i ≡ max (x ∷ xs) (s≤s z≤n))
min-finder x [] = fzero , refl
min-finder x (x′ ∷ xs) with x ≤? max (x′ ∷ xs) (s≤s z≤n)
min-finder x (x′ ∷ xs) | yes x≤y = increase x x′ xs x≤y (min-finder x′ xs)
min-finder x (x′ ∷ xs) | no y≤x = fzero , lemma x (x′ ∷ xs) (s≤s z≤n) (¬x≤y⇒y≤x y≤x)

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


\todo{fix references below}
\label{decidable-def}
