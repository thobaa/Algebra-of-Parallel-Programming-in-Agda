%if False
\begin{code}
--open import Relation.Binary
open import Relation.Binary
--open import Algebra.Equivalence this should not be used maybe
open import Agda.CH
module Algebra.Monoid where
\end{code}
%endif
In Agda, we again define a record datatype for the proposition |IsMonoid|: \todo{THOMAS: Remove ``CARRIER''} \todo{THOMAS: order of axioms in record}
\begin{code}
record IsMonoid {M : Set} (_≈_ : M → M → Set) (_∙_ : M → M → M) (e : M) : Set where
  field
    isEquivalence : IsEquivalence _≈_
    assoc : ∀ x y z → ((x ∙ y) ∙ z) ≈ (x ∙ (y ∙ z))
    identity : (∀ x → (e ∙ x) ≈ x) ∧ (∀ x → (x ∙ e) ≈ x)
    ∙-cong : ∀ {x x' y y'} → x ≈ x' → y ≈ y' → (x ∙ y) ≈ (x' ∙ y')
\end{code}
When we define our monoids, we add a derived property, setoid, which lets us use monoids in equational reasoning, see Section \ref{Section-where-eqr-helper-is-defined}. \todo{THOMAS: what are they called (derived property??)?} \todo{THOMAS: do we do this with groups too?, or if not, say so!}
\begin{code}
record Monoid : Set₁ where
  infix 7 _∙_
  infix 4 _≈_
  field
    M         : Set
    _≈_       : M → M → Set
    _∙_       : M → M → M
    e         : M
    isMonoid  : IsMonoid _≈_ _∙_ e
  open IsMonoid isMonoid public
  setoid : Setoid _ _
  setoid = record { isEquivalence = isEquivalence }
\end{code}

An example of a monoid (that are not groups) used in mathematics is the natural numbers, with dot as either multiplication or addition. Another is sets ($M$ is a collection of sets, dot is union). An example from computer science is lists ($M$ is a collection of lists, dot is list concatenation), which are very common in functional programming. \todo{THOMAS: where should this be}

We also define commutative monoids, that is, monoids where $a \cdot b = b \cdot a$ for every $a$, $b \in M$. We begin with the proposition that something is a commutative monoid: 
\begin{code}
record IsCommutativeMonoid {A : Set} (_≈_ : A → A → Set) (_∙_ : A → A → A) (e : A) : Set where
  field 
    isMonoid  : IsMonoid _≈_ _∙_ e
    comm      : ∀ x y → (x ∙ y) ≈ (y ∙ x)

  open IsMonoid isMonoid public
\end{code}
In the above definition, we take a slightly different approach than the Agda Standard Library in that we require the user to provide a proof that the operations form a monoid, which in turn requires a proof that |e| is an identity element of |_∙_|:
\begin{spec}
(∀ x → (e ∙ x) ≈ x) ∧ (∀ x → (x ∙ e) ≈ x)
\end{spec}
while thanks to commutativity, it would be enough to prove only one of the conjuncts. 

Next we define the datatype of commutative monoids: 
\begin{code}
record CommutativeMonoid : Set₁ where
  infixl 7  _∙_ 
  infix 4   _≈_
  field
    M        : Set
    _≈_      : M → M → Set
    _∙_      : M → M → M
    e        : M
    isCommutativeMonoid : IsCommutativeMonoid _≈_ _∙_ e

  open IsCommutativeMonoid isCommutativeMonoid public

  monoid : Monoid
  monoid = record { isMonoid = isMonoid }

  open Monoid monoid public using (setoid)
\end{code}

Commutative monoids are one of the datatypes we will use the most, in particular, we will want to prove equalities among members of a commutative monoid. To allow easy access to the equational reasoning module from the standard library, we import the |EqReasoning|-module and give it an the alias |EqR|:
\begin{code}
import Relation.Binary.EqReasoning as EqR
\end{code}
Then we make the following definition:\todo{THOMAS: GLOBAL: make sure all alignment is good}
\begin{code}
module CM-Reasoning (cm : CommutativeMonoid) where
  open CommutativeMonoid cm
  open EqR setoid
\end{code}

To prove a simple lemma, we then do the following \todo{THOMAS: either find a lemma to prove here, or refer forward}. For more complicated lemmas, or when there is a large number of them, there are automated approaches to proving equalities in commutative monoids in Agda, but they were not used for this thesis. \todo{THOMAS: perhaps good note in discussion}
%http://www.galois.com/~emertens/monoidsolver/MonoidSolver.html
%https://personal.cis.strath.ac.uk/conor.mcbride/pub/Hmm/CMon.agda
