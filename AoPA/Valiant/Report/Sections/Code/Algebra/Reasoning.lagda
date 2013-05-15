%if False
\begin{code}
open import Algebra.Monoid
open import Algebra.NANRing
import Relation.Binary.EqReasoning as EqR
module Algebra.Reasoning where
\end{code}
%endif
\begin{code}
module CM-Reasoning (cm : CommutativeMonoid) where
  open CommutativeMonoid public
--  open EqR setoid public

module NANR-Reasoning (nanr : NonAssociativeNonRing) where
  open NonAssociativeNonRing nanr public
  open EqR setoid public
\end{code}