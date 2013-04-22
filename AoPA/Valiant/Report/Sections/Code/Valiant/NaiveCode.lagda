%if False
\begin{code}
open import Data.Nat
open import Algebra.NANRing
module Valiant.NaiveCode (NANR : NonAssociativeNonRing) where -- also known as first attempt, perhaps a better name
open NonAssociativeNonRing NANR renaming (_+_ to _R+_)
\end{code}
%endif
The naive (and not the way we finally decide on, for reasons that become clear later, hence we add a |′| to the datatypes) way, which stays close to the |Vector| and |Matrix| datatypes would be to define |Vec′| as something like
\begin{code}
data Vec′ : ℕ → Set where
  one : (x : Carrier) → Vec′ 1 
  two : {m n : ℕ} → Vec′ m → Vec′ n → Vec′ (m + n)
\end{code}
and then defining |Mat′| as \todo{should we call |Vec′| |Vec| or |Vec′| in text, and code?}
\begin{code}
data Mat′ : ℕ → ℕ → Set where
  sing : (x : Carrier) → Mat′ 1 1
  rVec : {n : ℕ} → Vec′ (suc (suc n)) → Mat′ 1 (suc (suc n)) 
  cVec : {n : ℕ} → Vec′ (suc (suc n)) → Mat′ (suc (suc n)) 1
  quad : {r₁ r₂ c₁ c₂ : ℕ} → Mat′ r₁ c₁ → Mat′ r₁ c₂ → 
                             Mat′ r₂ c₁ → Mat′ r₂ c₂ → Mat′ (r₁ + r₂) (c₁ + c₂)
\end{code}
Where we name the indices |r₁|, |r₂|, |c₁| and |c₂| to for rows and columns of the involved matrices, and the ordering is so that we can write it on two rows.

While this looks like a very natural way to define the datatypes, it will not work well when we want to prove things about the matrices. As we have mentioned before, the main way to prove things in Agda is to use structural induction by pattern matching on the structures involved. However, if we pattern match on a |Mat′|, one problem that appears is that Agda is unable to see that in the |quad| case, both indices must be at least |2|, nor that both terms |a| and |b| have to be at least |1|. It is possible to write lemmas proving this, and use them at every step. However, there are worse cases, when Agda's ability to unify indices won't help us when doing more complicated things, like realizing that some integer |n| is equal to |a + b|, also, we can't tell whether |a| is a sum or not, so the second splitting step is complicated, for example \todo{include short example}.
