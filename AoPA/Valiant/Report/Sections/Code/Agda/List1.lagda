For example, we could define Lists as 
%if False
\begin{code}
module List1 where
\end{code}
%endif
\begin{code}
infixr 8 _∷_
data [_] (a : Set) : Set where
  []   : [ a ]
  _∷_ : (x : a) → (xs : [ a ]) → [ a ]
\end{code}
The notation here is very similar to the Haskell notation for lists, with the diffrerence that we need to use spaces between the brackets and |a| (the reason for this is that |[a]|, without spaces is a valid type identifier in Agda.

We also define a type of natural numbers, so we have some type to make Lists of. Here we take advantage of Agdas ability to use any unicode symbols to give the type a short and familiar name:
\begin{code}
data ℕ : Set where
  zero : ℕ
  suc  : (n : ℕ) → ℕ
\end{code}
If we use the commands following commands
\begin{code}
{-# BUILTIN NATURAL ℕ    #-}
{-# BUILTIN ZERO    zero #-}
{-# BUILTIN SUC     suc  #-}
\end{code}
we can write the natural numbers with digits, and define a list 
\begin{code}
exampleList : [ ℕ ]
exampleList = 5 ∷ 2 ∷ 12 ∷ 0 ∷ 23 ∷ []
\end{code}