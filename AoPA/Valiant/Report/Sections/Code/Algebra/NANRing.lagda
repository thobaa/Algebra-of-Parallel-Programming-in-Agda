%if False
\begin{code}
open import Algebra.Equivalence
open import Algebra.Distributive
module Algebra.NANRing where
\end{code}
%endif

\begin{code}
record NonAssociativeNonRing : Set₁ where
  infix 5 _+_ 
  infix 10 _*_
  field 
    Carrier : Set
    _≈_ : Rel Carrier
    _+_ : Op₂ Carrier
    _*_ : Op₂ Carrier
    0#  : Carrier
    --isNonAssociativeNonRing : isNonAssociativeNonRing _≈_ _+_ _*_ 0#
\end{code}