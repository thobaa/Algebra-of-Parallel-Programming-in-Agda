%if False
\begin{code}
open import Algebra.Equivalence
open import Agda.CH 
open import Algebra.Monoid
module Algebra.NANRing where
\end{code}
%endif
In Agda, we begin by defining the proposition that something is a \nanring:
\savecolumns
\begin{code}
record IsNonAssociativeNonRing {R : Set} (_≈_ : R → R → Set) (_+_ _*_ : R → R → R) (R0 : R) : Set₁ where
  field
    +-isCommutativeMonoid  : IsCommutativeMonoid _≈_ _+_ R0
    *-cong                 : ∀ {x x' y y'} → x ≈ x' → y ≈ y' → (x * y) ≈ (x' * y')
    distrib                : (∀ x y z → (x * (y + z)) ≈ ((x * y) + (x * z))) ∧ (∀ x y z → ((y + z) * x) ≈ ((y * x) + (z * x)))
    zero                   : (∀ x → (R0 * x) ≈ R0) ∧ (∀ x → (x * R0) ≈ R0)
\end{code}
Next, we want the ability to use the axioms we get from the fact that |_+_| is a commutative monoid, we do this by openening the |IsCommutativeMonoid|-record, the |public| keyword opens it to the world when |IsNonAssociativeNonRing| is opened.
\restorecolumns
\begin{code}  
  open IsCommutativeMonoid +-isCommutativeMonoid public
         renaming  (  assoc               to +-assoc
                   ;  ∙-cong              to +-cong
                   ;  identity            to +-identity
                   ;  isMonoid            to +-isMonoid
                   ;  comm                to +-comm
                   )
\end{code}
Then, we want to open all the simpler structures involved, so that we can use the axioms related to the fact that addition is a commutative monoid.

Then, we define the record datatype containing all \nanring s:
\savecolumns
\begin{code}
record NonAssociativeNonRing : Set₁ where
  infix 4   _≈_
  infix 5   _+_ 
  infix 10  _*_
  field 
    R    : Set
    _≈_  : R → R → Set
    _+_  : R → R → R
    _*_  : R → R → R
    R0   : R
    isNonAssociativeNonRing : IsNonAssociativeNonRing _≈_ _+_ _*_ R0
  open IsNonAssociativeNonRing isNonAssociativeNonRing public
\end{code}
We want to be able to access the fact that it is a commutative monoid with |_+_|, so we give this a name and open it:
\restorecolumns
\begin{code}
  +-commutativeMonoid : CommutativeMonoid
  +-commutativeMonoid = record { isCommutativeMonoid = +-isCommutativeMonoid }
  
  open CommutativeMonoid +-commutativeMonoid public using (setoid) 
                         renaming (monoid     to +-monoid)
\end{code}

As with the commutative monoids, we will spend a bit of time proving equalities of \nanring elements, so we define:
%if False
\begin{code}
import Relation.Binary.EqReasoning as EqR
\end{code}
%endif
\begin{code}
module NS-Reasoning (ns : NonAssociativeNonRing) where
  open NonAssociativeNonRing ns
  open EqR setoid
\end{code}
