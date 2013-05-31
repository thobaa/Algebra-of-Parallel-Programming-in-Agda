%if False
\begin{code}
open import Data.Nat
open import Algebra.NANRing
module Valiant.NaiveCode (NaSr : NonassociativeSemiring) where -- also known as first attempt, perhaps a better name
open NonassociativeSemiring NaSr renaming (_+_ to _R+_)
\end{code}
%endif
The naive way (and not the way we finally decide on, for reasons that become clear later, hence we add an apostrophe to the datatype names), which stays close to the |Vector| and |Matrix| datatypes would be to define |Vec'| as something like
\begin{code}
data Vec' : ℕ → Set where
  one  : R → Vec' 1 
  two  : {m n : ℕ} → Vec' m → Vec' n → Vec' (m + n)
\end{code}
and then defining |Mat'| as 
\begin{code}
data Mat' : ℕ → ℕ → Set where
  sing  : R → Mat' 1 1
  rVec  : {n : ℕ} → Vec' (suc (suc n)) → Mat' 1 (suc (suc n)) 
  cVec  : {n : ℕ} → Vec' (suc (suc n)) → Mat' (suc (suc n)) 1
  quad  : {r₁ r₂ c₁ c₂ : ℕ}  →  Mat' r₁ c₁ →  Mat' r₁ c₂ → 
                                Mat' r₂ c₁ →  Mat' r₂ c₂ 
                             → Mat' (r₁ + r₂) (c₁ + c₂)
\end{code}
Finally, to define |Tri'| is straightforward. There is only one base case, that of the $1 \times 1$ zero triangle, with constructor |zer|. We only need one size argument since it is a square matrix.
\begin{code}
data Tri' : ℕ → Set where
  zer  : Tri' 1
  tri  : {m n : ℕ} → Tri' m  →  Mat' m n → 
                                Tri' n   
                               → Tri' (m + n)
\end{code}
While the above looks very natural, it will not work well when we want to prove things about the matrices. If we pattern match on a |Mat'|, one problem that appears is that Agda is unable to see that in the |quad| case, both indices must be at least |2|, and that both |r₁| and |r₂| (say) have to be at least |1|. It is possible to write lemmas proving this, and use them at every step, but this clutters the proofs. Additionally,  when Agda will be unable to infer for example that the different parts have been built the same way. For example when trying to define the overlap row step, $m = 1$, $n > 1$ we pattern match on |R| and |L|, and Agda infers that they have sizes |x + y| and |x' + y' |, but cannot infer (since it need not be true) that their |x| equals |x'| and |y| equals |y'|, which is required to compute the overlap for the parts of |R| recursively.
