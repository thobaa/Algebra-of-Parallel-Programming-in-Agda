%if False
\begin{code}
open import Data.Nat
module Proof where

-- _<_ : ℕ → ℕ → Set
-- m < n = suc m ≤ n

data [_] (a : Set) : Set where
  []   : [ a ]                
  _∷_  : a → [ a ] → [ a ]     

length : {a : Set} → [ a ] → ℕ
length [] = zero
length (x ∷ xs) = suc (length xs)
max : ℕ → ℕ → ℕ
max zero n = n
max (suc n) zero = suc n
max (suc n) (suc n') = suc (max n n')

maxL : (xs : [ ℕ ]) → (0 < length xs) → ℕ
maxL []               ()
maxL (x ∷ [])         _ = x
maxL (x ∷ (x' ∷ xs))  _ = max x (maxL (x' ∷ xs) (s≤s z≤n))

data Fin : ℕ → Set where
  f0     : {n : ℕ} → Fin (suc n)
  fsuc   : {n : ℕ} → Fin n → Fin (suc n)

infix 10 _‼_
_‼_ : ∀ {a} → (xs : [ a ]) → (n : Fin (length xs)) → a
[]         ‼ ()
(x ∷ xs)   ‼ f0       = x
(x ∷ xs)   ‼ fsuc i   = xs ‼ i
\end{code}
%endif
\begin{code}
-- general lemmas about |_≤_|:
≤-refl : {n : ℕ} → n ≤ n
≤-refl  {0}      = z≤n
≤-refl  {suc n}  = s≤s ≤-refl

≤-trans : {i j k : ℕ} → i ≤ j → j ≤ k → i ≤ k
≤-trans  z≤n          j≤k          = z≤n
≤-trans  (s≤s a≤b)    (s≤s b≤c)    = s≤s (≤-trans a≤b b≤c)

-- properties of |max|
max-≤₁ : {m n : ℕ} → m ≤ max m n
max-≤₁  {0}       {n}        = z≤n
max-≤₁  {suc k}   {0}        = ≤-refl
max-≤₁  {suc k}   {suc l}    = s≤s max-≤₁

max-≤₂ : {m n : ℕ} → n ≤ max m n
max-≤₂  {m}      {0}       = z≤n
max-≤₂  {0}      {suc l}   = ≤-refl
max-≤₂  {suc k}  {suc l}   = s≤s (max-≤₂ {k})


-- base case
max-greatest-base : (x : ℕ) (xs : [ ℕ ]) → x ≤ maxL (x ∷ xs) (s≤s z≤n)
max-greatest-base  x  []         = ≤-refl
max-greatest-base  x  (x' ∷ xs)  = max-≤₁

-- the proof
max-greatest :  (xs : [ ℕ ]) → (pf : 0 < length xs) → 
                (i : Fin (length xs)) → xs ‼ i ≤ maxL xs pf
max-greatest  []                 ()         _
max-greatest  (x ∷ xs)           (s≤s z≤n)  f0          =  max-greatest-base x xs
max-greatest  (x ∷ [])           (s≤s z≤n)  (fsuc ())
max-greatest  (x ∷ (x' ∷ xs))    (s≤s z≤n)  (fsuc i)    =  ≤-trans 
                                                             (max-greatest _ _ i)
                                                             (max-≤₂ {x})
\end{code}
