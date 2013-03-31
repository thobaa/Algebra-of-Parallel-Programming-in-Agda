%if False
\begin{code}
module GroupDef where
open import FunctionDefs
\end{code}
%endif
In Agda code, we define the proposition |IsGroup|, that states that something is a group. We define this using a record \todo{include that Agda records somewhere in Agda section} so that we can give names to the different lemmas, because when reasoning about an arbitrary group (which we will define shortly), the only thing we have are these lemmas.\todo{make note that we have taken names from standard library but use less general/simpler definitions}
\begin{code}
record IsGroup {G : Set} (_≈_ : G → G → Set) (_∙_ : G → G → G) (e : G) (_⁻¹ : G → G) : Set where
  field
    isEquivalence : IsEquivalence _≈_
    
\end{code}
We note that we need to include the equality in the definition of the group along with the fact that it should be an equivalence relation, this is usually not mentioned in a mathematical definitions of a group, but is necessary here, because the structural equality \todo{is this the word, is it used before---should be mentioned when introducing refl} of the type |G| is not necessarily the equality we want for the group (as not all sets are inductively defined).

We can then define the type |Group|, containing all groups with a record, so that we can have names for the different fields. Note that the type of |Group| is |Set₁|, because like |Set|, |Group| is ``too big'' to be in |Set| (if we want to avoid things like Russel's Paradox).
\begin{code}
record Group : Set₁ where
  infix 7 _∙_
  infix 4 _≈_
  field
    Carrier : Set
    _≈_     : Carrier → Carrier → Set
    _∙_     : Carrier → Carrier → Carrier
    e       : Carrier
    _⁻¹     : Carrier → Carrier
    isGroup : IsGroup _≈_ _∙_ e _⁻¹
\end{code}
The things to note here are that 
Where we have both defined the various elements required in a group, along with the axioms they need to satisfy.
