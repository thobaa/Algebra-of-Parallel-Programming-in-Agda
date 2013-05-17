%if False
\begin{code}
--open import Relation.Binary
open import Relation.Binary
--open import Algebra.Equivalence this should not be used maybe
open import Data.Product renaming (_×_ to _∧_)
module Algebra.Monoid where
\end{code}
%endif
In Agda, we again define a record datatype for the proposition |IsMonoid|:
\begin{code}
record IsMonoid {M : Set}  (_≈_ : M → M → Set) (_∙_ : M → M → M) 
                           (e : M) : Set where
  field
    isEquivalence : IsEquivalence _≈_
    ∙-cong    : ∀ {x x' y y'} → x ≈ x' → y ≈ y' → (x ∙ y) ≈ (x' ∙ y')
    assoc     : ∀ x y z → ((x ∙ y) ∙ z) ≈ (x ∙ (y ∙ z))
    identity  : (∀ x → (e ∙ x) ≈ x) ∧ (∀ x → (x ∙ e) ≈ x)
\end{code}
The set |M| is sometimes called the \emph{carrier} of the monoid (or any other structure). The Agda Standard Library uses this name.

We note that we need to include the equality in the definition of the group along with the fact that it should be an equivalence relation, this is usually not mentioned in a mathematical definitions of a group, but is necessary here, because the structural equality \todo{is this the word, is it used before---should be mentioned when introducing refl} of the type |G| is not necessarily the equality we want for the group (as not all sets are inductively defined).

We can then define a record for the type |Monoid|, containing all monoids. Note that the type of |Monoid| is |Set₁|, because like |Set|, |Monoid| is ``too big'' to be in |Set|.
\begin{code}
record Monoid : Set₁ where
  field
    M         : Set
    _≈_       : M → M → Set
    _∙_       : M → M → M
    e         : M
    isMonoid  : IsMonoid _≈_ _∙_ e

  open IsMonoid isMonoid public
\end{code}
%if False
\begin{code}
  infix 7 _∙_
  infix 4 _≈_
\end{code}
%endif
We  added the line |open IsMonoid isMonoid public| in the record to put the |IsMonoid| definitions in scope when the |Monoid| record is opened. 
We also add a definition |setoid| to our monoid record, which lets us use monoids in equational reasoning, see Section \ref{Section-where-eqr-helper-is-defined}.
\begin{code}
  setoid : Setoid _ _
  setoid = record { isEquivalence = isEquivalence }
\end{code}
We also add a definition |setoid| to our monoid record, which lets us use monoids in equational reasoning, see Section \ref{Section-where-eqr-helper-is-defined}.

To prove something is a monoid, we thus construct an inhabitant of the type |IsMonoid|. We usually also give the monoid record containing the object a name, to allow us to use it in places where a monoid is wanted.

Example of a monoids (that are not groups) include the natural numbers, with $\cdot$ as either multiplication or addition, sets ($M$ is a collection of sets, $\cdot$ is union), lists ($M$ is a collection of lists, $\cdot$ is list concatenation).

We now define commutative monoids. We begin with the proposition that something is a commutative monoid: 
\begin{code}
record IsCommutativeMonoid  {A : Set} (_≈_ : A → A → Set) 
                            (_∙_ : A → A → A) (e : A) : Set where
  field 
    isMonoid  : IsMonoid _≈_ _∙_ e
    comm      : ∀ x y → (x ∙ y) ≈ (y ∙ x)

  open IsMonoid isMonoid public
\end{code}
As in the definition of |Monoid|, we open the |IsMonoid| record here to move the properties of a |Monoid| into scope.

In the definition of |IsCommutative|, we are taking a slightly different approach than the Agda Standard Library: we require the user to provide a proof that the operations form a monoid, which in turn requires a proof that |e| is an identity element of |_∙_|:
\begin{spec}
(∀ x → (e ∙ x) ≈ x) ∧ (∀ x → (x ∙ e) ≈ x)
\end{spec}
while because of commutativity, it would be enough to prove only one of the conjuncts. 

Next we define the datatype of commutative monoids: 
\begin{code}
record CommutativeMonoid : Set₁ where
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
%if False
\begin{code}
  infixl 7  _∙_ 
  infix 4   _≈_
\end{code}
%endif
Commutative monoids are one of the datatypes we will use the most, in particular, we will want to prove equalities among members of a commutative monoid. To allow easy access to the equational reasoning module from the Agda Standard Library, we import the |EqReasoning| module and give it an the alias |EqR|:
\begin{code}
import Relation.Binary.EqReasoning as EqR
\end{code}
Then we make the following definition:
\begin{code}
module CM-Reasoning (cm : CommutativeMonoid) where
  open CommutativeMonoid cm public
  open EqR setoid public
\end{code}
So that the module |CM-Reasoning| takes a commutative monoid and brings into scope the commutative monoid axioms and the contents of the |EqReasoning| module.
As an example of equational reasoning, we prove a simple lemma with it:
\begin{code}
0′+0″≈0 : (cm : CommutativeMonoid) → let open CommutativeMonoid cm renaming (_∙_ to _+_) in {0′ 0″ : M} → 0′ ≈ e → 0″ ≈ e → 0′ + 0″ ≈ e
0′+0″≈0 cm {0′} {0″} 0′≈0 0″≈0  = begin 
  0′ + 0″ 
    ≈⟨ ∙-cong 0′≈0 0″≈0 ⟩ 
  e + e
    ≈⟨ proj₁ identity e ⟩
  e ∎
  where open CM-Reasoning cm renaming (_∙_ to _+_)
\end{code}
For more complicated lemmas, or in case large number of lemmas, there are automated approaches to proving equalities in commutative monoids in Agda, but they were not used for this thesis. \todo{THOMAS: perhaps good note in discussion, also give a reference}
%http://www.galois.com/~emertens/monoidsolver/MonoidSolver.html
%https://personal.cis.strath.ac.uk/conor.mcbride/pub/Hmm/CMon.agda
