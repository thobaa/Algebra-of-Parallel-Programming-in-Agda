%if False
\begin{code}
open import Algebra.Equivalence
open import Algebra.ShortDefs
open import Data.Nat using ()
open import Algebra.Monoid
open import Data.Product using () renaming (_×_ to _∧_)
module Algebra.NANRing where
\end{code}
%endif
In Agda, we begin by defining the proposition that something is a nonassociative semiring, with operations |_+_| and |_*_| and additive identity |R0|. We open the |IsCommutativeMonoid| record for |_+_|, and prefix the ones referring to addition with |+-|.
\savecolumns
\begin{code}
record IsNonassociativeSemiring  {R : Set}  (_≈_ : R → R → Set) 
                                            (_+_ _*_ : R → R → R) 
                                            (R0 : R) : Set₁ where
  field
    *-cong       :  ∀ {x x' y y'} → x ≈ x' → y ≈ y' → (x * y) ≈ (x' * y')

    +-isCommutativeMonoid  : IsCommutativeMonoid _≈_ _+_ R0

    distrib      :  Distributive _≈_ _*_ _+_ 
    zero         :  Zero _≈_ R0 _*_

  open IsCommutativeMonoid +-isCommutativeMonoid public
         renaming  (  assoc               to  +-assoc
                   ;  ∙-cong              to  +-cong
                   ;  identity            to  +-identity
                   ;  isMonoid            to  +-isMonoid
                   ;  comm                to  +-comm
                   )
\end{code}
Then, we define the record datatype containing all nonassociative semirings:
\savecolumns
\begin{code}
record NonassociativeSemiring : Set₁ where
  field 
    R    : Set
    _≈_  : R → R → Set
    _+_  : R → R → R
    _*_  : R → R → R
    R0   : R
    isNonassociativeSemiring : IsNonassociativeSemiring _≈_ _+_ _*_ R0
  open IsNonassociativeSemiring isNonassociativeSemiring public
\end{code}
%if False
\begin{code}
  infix 4   _≈_
  infix 5   _+_ 
  infix 10  _*_
\end{code}
%endif
We want to be able to access the fact that it is a commutative monoid with |_+_|, so we give this a name and open it:
\restorecolumns
\begin{code}
  +-commutativeMonoid : CommutativeMonoid
  +-commutativeMonoid   = record {  isCommutativeMonoid = 
                                    +-isCommutativeMonoid }
  
  open CommutativeMonoid +-commutativeMonoid public using (setoid) 
                         renaming (monoid     to +-monoid)
\end{code}

As with the commutative monoids, we will spend a bit of time proving equalities of nonassociative semiring elements, so we define a module similar to the one in Section \ref{CM-EqReasoning}:
%if False
\begin{code}
import Relation.Binary.EqReasoning as EqR
\end{code}
%endif
\begin{code}
module NS-Reasoning (ns : NonassociativeSemiring) where
  open NonassociativeSemiring ns public
  open EqR setoid public
\end{code}
