%if False
\begin{code}
module Agda.List1 where
\end{code}
%endif
First, we need to define the datatype of natural numbers, which we denote by the unicode character |ℕ|).
\begin{code}
data ℕ  : Set where
  zero  : ℕ
  suc   : ℕ → ℕ
\end{code}
This datatype has two constructors, |zero| and |suc|. |suc| is a function taking a natural number as input and returning what is to be thought of as the successor of the number. For example, we can define
\begin{code}
one : ℕ
one = suc zero

five : ℕ
five = suc (suc (suc (suc (suc zero))))
\end{code}
This is a fairly cumbersome way of writing numbers, and it is possible to make Agda support a more standard notation for |ℕ| using the pragmas
\begin{code}
{-# BUILTIN NATURAL   ℕ      #-}
{-# BUILTIN ZERO      zero   #-}
{-# BUILTIN SUC       suc    #-}
\end{code}
so that we may write:
\begin{code}
two  : ℕ
two  = 2
\end{code}
Next, we define lists, 

\begin{code}
infixr 8 _∷_
data [_] (a : Set) : Set where
  []   : [ a ]
  _∷_  : a → [ a ] → [ a ]
\end{code}
We have chosen the notation to be similar to the Haskell notation for lists. The |(a : Set)| before the colon means the type of lists depends on a parameter, which is an arbitrary (small) type |a|. The underscore denotes where the argument is placed, so |[ a ]| is a list of elements from |a|, |[ ℕ ]| a list of natural numbers, etc. In the same way, |_∷_| is a function of two arguments, the first of type |a| (written in the place of the first underscore), the second of type |[ a ]| (written in place of the second underscore). The line |infixr 8 _∷_| explains that the infix operator |_∷_| associates to the right (the |r|) and the |8| defines how tightly it binds (to determine whether an expression including other operators needs parentheses or not). In the remainder we omit the |infix| declarations from this text, but use them to give operations the bindings we expect (so that, for example, multiplication binds tighter than addition). 

We give an example of a list of natural numbers:
\begin{code}
exampleList  : [ ℕ ]
exampleList  = 5 ∷ 2 ∷ 12 ∷ 0 ∷ 23 ∷ []
\end{code}

Next, we define some functions on |ℕ| and |[ ℕ ]|. In particular, to define the maximum over a list of natural numbers, we need to be able to find the maximum of a pair of natural numbers. We define this as follows:
\begin{code}
max : ℕ → ℕ → ℕ
max zero     n        = n
max (suc m)  zero     = suc m
max (suc m)  (suc n)  = suc (max m n)
\end{code}
Here, we need to pattern match on both variables. The first variable is either |zero| or |suc m|, for some |m|. In the first case, we know that the maximum is the second argument. In the second case, we must pattern match on the second variable. If it is |zero|, we are again done. If it is |suc n| for some |n|, we recursively find |max m n| (note that |max| is called with two arguments, both of which contain one fewer applications of |suc|, so the recursion will terminate, eventually), and increase it.

Next, we want to define a function |maxL| that returns the maximum of a list. We decide to only define |maxL| on nonempty lists. It could be argued that |maxL [] = 0| is sensible, but if we were to generalize the definition to  an arbitrary total order on an arbitrary type, in general, there is no least element  (just consider the integers |ℤ|. We still want to use the same datatype, of lists though (we could assume that we have built a large library that depends on them).

To force the list to be non-empty, we want |maxL| to take two arguments, the first of which is a list |xs|, and the second of which is a proof that the length of |xs| is greater than $0$. Writing the function |length| for |ℕ| should be easy by now, so we decide to write it for arbitrary types |a|:
\begin{code}
length : {a : Set} → [ a ] → ℕ
length [] = zero
length (x ∷ xs) = suc (length xs)
\end{code}
Here, the |{a : Set}| means that |a| is an implicit argument to the function (that Agda can infer by looking at the type of |x| in this case). The fact that |a| is given a name and appears in the types following it means that the types depend on the value of |a|, and this, in part is what it means to be a dependently typed language (more generally, the fact that we can give any function argument a name and have the types following it contain it), this is an example of a dependent function space. We write |(a : Set)| if we wanted |a| to be an explicit named argument. It is also possible to define multiple elements, say |a|, |b|, |c|, of the same type |A| by writing |{a b c : A}| or |(a b c : A)|.

Implicit arguments are provided in curly brackets, so we can define a length-function for |ℕ| by partial application:
\begin{code}
lengthℕ : [ ℕ ] → ℕ
lengthℕ = length {ℕ}
\end{code}

In the next section, we discuss the second part of what we need to give the type of |maxL|, that is, a way to define proofs in Agda.
