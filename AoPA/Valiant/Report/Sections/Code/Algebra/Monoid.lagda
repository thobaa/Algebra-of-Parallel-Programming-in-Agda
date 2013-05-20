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
\savecolumns
\begin{code}
record IsMonoid {M : Set}  (_≈_ : M → M → Set) (_∙_ : M → M → M) 
                           (e : M) : Set where
  field
    isEquivalence : IsEquivalence _≈_
    ∙-cong    : ∀ {x x' y y'} → x ≈ x' → y ≈ y' → (x ∙ y) ≈ (x' ∙ y')
    assoc     : ∀ x y z → ((x ∙ y) ∙ z) ≈ (x ∙ (y ∙ z))
    identity  : (∀ x → (e ∙ x) ≈ x) ∧ (∀ x → (x ∙ e) ≈ x)
\end{code}
We add the line 
\restorecolumns
\begin{code}
  open IsEquivalence isEquivalence public
\end{code}
in the record to put the fields from |IsEquivalence| in scope when the |IsMonoid| record is opened.

The set |M| is sometimes called the \emph{carrier} of the monoid (or any other structure), and the Agda Standard Library uses this name.

We note that we need to include the the equality |_≈_| along with the fact that it should be an equivalence relation in the definition. We also want a proof that |∙-cong| that the operation and the equality interact nicely, if |x| and |x'| are equal and |y| and |y'| are equal, then |x ∙ y| and |x' ∙ y'| should be equal. \todo{THOMAS: should cong be mentioned in the introductory defs section? NO?}

We can then define a record for the type |Monoid|, containing all monoids. Note that the type of |Monoid| is |Set₁|, because like |Set| itself, |Monoid| is ``too big'' to be in |Set|.
\savecolumns
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
We also add a definition |setoid| to our monoid record, which lets us use monoids in equational reasoning, see Section \ref{Section-where-eqr-helper-is-defined}.
\restorecolumns
\begin{code}
  setoid : Setoid _ _
  setoid = record { isEquivalence = isEquivalence }
\end{code}

To prove something is a monoid, we construct an inhabitant of the type |IsMonoid|. We usually also give the monoid record containing the object a name, to be able to use it in places where a monoid is wanted, as in Section \ref{Section where monoids (or something) are defined}.

We now define commutative monoids. We begin with the proposition that something is a commutative monoid. The proposition contains a proof that it is a monoid and a proof that the operation is commutative, and we open the |IsMonoid| record so that the proofs that the structure is a monoid are in scope.
\begin{code}
record IsCommutativeMonoid  {A : Set} (_≈_ : A → A → Set) 
                            (_∙_ : A → A → A) (e : A) : Set where
  field 
    isMonoid  : IsMonoid _≈_ _∙_ e
    comm      : ∀ x y → (x ∙ y) ≈ (y ∙ x)

  open IsMonoid isMonoid public
\end{code}

In the definition of |IsCommutative|, we are taking a slightly different approach than the Agda Standard Library: we require the user to provide a proof that the operations form a monoid, which in turn requires a proof that |e| is an identity element of |_∙_|:
\begin{spec}
(∀ x → (e ∙ x) ≈ x) ∧ (∀ x → (x ∙ e) ≈ x)
\end{spec}
while because of commutativity, |x ∙ e ≈ e ∙ x|, so it would be enough to require a proof of just one of the conjuncts. 

Next we define the datatype of commutative monoids, and open the records so that all definitions are in scope: %(we need to take care to not open a record twice, since that would lead to 
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
\subsubsection{Equational Reasoning in Commutative Monoids}
\label{CM-EqReasoning}
\label{Section-where-eqr-helper-is-defined}.
Commutative monoids are one of the datatypes we will use the most, in particular, we will want to prove equalities among members of a commutative monoid. The Agda Standard Library contains a module |EqReasoning| that lets us reason about equalities using a very natural syntax. To allow easy access to this module, we we import itgive it an the alias |EqR|:
\begin{code}
import Relation.Binary.EqReasoning as EqR
\end{code}
and make the following module definition:
\begin{code}
module CM-Reasoning (cm : CommutativeMonoid) where
  open CommutativeMonoid cm public
  open EqR setoid public
\end{code}
So that the module |CM-Reasoning| takes a commutative monoid as a parameter and brings into scope the commutative monoid axioms and the contents of the |EqReasoning| module. We often use this module locally, using a |where|-definition.

As an example of equational reasoning, we prove a simple lemma with it, that if two elements in a commutative monoid are equal to the identity element, then so is their sum. We use a |let| statement in the type to open the record |CommutativeMonoid| locally and make the type more readable.
\label{e'e''e}
\begin{code}
e'∙e''≈e : (cm : CommutativeMonoid) → 
  let open CommutativeMonoid cm in 
  {e' e'' : M} → e' ≈ e → e'' ≈ e → e' ∙ e'' ≈ e
e'∙e''≈e cm {e'} {e''} e'≈e e''≈e = begin 
  e' ∙ e'' 
    ≈⟨ ∙-cong e'≈e e''≈e ⟩ 
  e ∙ e
    ≈⟨ proj₁ identity e ⟩
  e ∎
  where open CM-Reasoning cm
\end{code}
On the first line (after |begin|), we write the expression on the left hand side of the equality we want to prove. Then, we write a sequence of expressions and proofs that the expressions are equal, ending with the expression on the right hand side, followed by |∎|.

The syntax makes the proof a lot easier to follow, and even more so with longer proofs. Without it, the proof would be written as:
\begin{spec}
e'∙e''≈e cm e'≈e e''≈e = trans (∙-cong e'≈e e''≈e) (proj₁ identity e)
\end{spec}
where |proj₁| is the projection that takes a pair to its first element.

For more complicated lemmas, or in case large number of lemmas, there are automated approaches to proving equalities in commutative monoids in Agda, but they were not used for this thesis. \todo{THOMAS: perhaps good note in discussion, also give a reference}
%http://www.galois.com/~emertens/monoidsolver/MonoidSolver.html
%https://personal.cis.strath.ac.uk/conor.mcbride/pub/Hmm/CMon.agda
