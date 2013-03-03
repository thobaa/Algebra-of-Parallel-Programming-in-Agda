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

We decide to only define the max function on nonempty lists (in the case of natural numbers, it might be sensible to define |max [] = 0|, but when it comes to other types, and orders, there is no least element).
 Second, we need to define . This is done with the following data type: 
\begin{code}
data _≤_ : ℕ → ℕ → Set where
  z≤n : {n : ℕ} → zero ≤ n
  s≤s : {m n : ℕ} → (m≤n : m ≤ n) → suc m ≤ suc n 
\end{code}
Here we introduce another feature of Agda, that functions can take implicit arguments, the constructor |z≤n| takes an argument |n|, but Agda can figure out what it is from the resulting type (which includes |n|), and hence, we don't need to include it.

Viewed through the Curry Howard Correspondence, the data type |m ≤ n| represents the proposition that |m| is less than or equal to |n|, and the two possible proofs of this are, either |m| is |zero|, which is less than any natural number, or |m = suc m'| and |n = suc n'| and we have a proof of |m' ≤ n'|.

Now we define the |length| function for lists, 
\begin{code}
length : ∀ {a} → [ a ] → ℕ
length [] = 0
length (x ∷ xs) = suc (length xs)
\end{code}
Here, again, we introduce a new concept, preceeding a variable with |∀| means that Agda infers its type (in this case |Set|).

Now, we can define the |max| function:
\begin{code}
max : (xs : [ ℕ ]) → 1 ≤ length xs  → ℕ
max [] ()
max (x ∷ []) _ = x
max (x ∷ (x' ∷ xs)) _ = maxℕ x (max (x' ∷ xs) (s≤s z≤n))
\end{code}
On the first line, we use the |()|-pattern to show that there is no proof that |1 ≤ 0|. On the second two lines, we don't care about what the input proof is (it is |s≤s z≤n| in both cases, so we use |_| to signify that it's not important). [TODO: NAmes of ()-pattern and |_|]

We also need an indexing function, and again, we only define it for sensible inputs:
\begin{code}
index : ∀ {a} → (xs : [ a ]) → (n : ℕ) → suc n ≤ length xs → a
index [] n ()
index (x ∷ xs) zero _ = x
index (x ∷ xs) (suc n) (s≤s m≤n) = index xs n m≤n
\end{code}

Now, we can write our specification of the |max| function.


The final step is defining equality, i.e., the proposition that two values |x| and |y| are equal. The basic equality is a data type whose only constructor |refl| is a proof that |x| is equal to itself.
\begin{code}
data _≡_ {a : Set} : a → a → Set where
  refl : {x : a} → x ≡ x
\end{code}
Herre, we have an implicit argument to the \emph{type}, to allow it to work for an type. For our purposes, this very strong concept of equality is suitable. However, if one wants to allow different ``representations'' of an object, for example if one defines the rational numbers as pairs of integers, |ℚ = ℤ × ℤ|, one wants a concept of equality that considers |(p , q)| and |(m * p , m * q)| to be  equal.
would want two numbers 
two sets where the elements were added in different order, or if one defines the rational numbers two rational numbers, $p/q$ and $(mp/mq)$, defined as pairs of natural numbers) to be equal, one would need an equality type with more constructors. For example
