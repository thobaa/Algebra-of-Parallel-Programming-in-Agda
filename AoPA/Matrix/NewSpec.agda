import Matrix.Abstract
import Matrix.Tri
import Matrix.NewNewSplit
open import Data.Nat hiding (_⊓_)
open import Data.Product
open import Relation.Binary.PropositionalEquality
--open import Relation.Binary
open import Data.Fin using (Fin; fromℕ; fromℕ≤; toℕ;  raise; reduce≥; inject₁) 
                     renaming (zero to f0; suc to fsuc)

open import Data.Unit
open import Level using () renaming (zero to Lzero)
open import Data.Vec renaming (zip to zipv; map to mapv)
open import Function

-- AOPA
open import Relations
open import Relations.Minimum
open import Relations.Coreflexive
open import Sets
open import AlgebraicReasoning.Relations

open import AlgebraicReasoning.Equality

-- END AOPA
open import Level using (Level) renaming (zero to Lzero)

open import Matrix.NonAssociativeRing

module Matrix.NewSpec (NAR : NonAssociativeRing Lzero Lzero) where

open Matrix.Abstract (NAR)
open Matrix.Tri (NAR)
open Matrix.NewNewSplit (NAR)

-- Non-associative powers
_T^[1+_] : ∀ {s} → Tri s → ℕ → Tri s
_T^[1+_] {s} T i = (foldr (λ _ → Tri s) _T+_ T ∘ (mapv (uncurry (_T*_))) ∘ (uncurry′ zipv) ∘ < id , reverse >) (allPrevious i)
  where
    allPrevious : (k : ℕ) -> Vec (Tri s) k
    allPrevious zero     = []
    allPrevious (suc n') = T T^[1+ n' ] ∷ allPrevious n'


sumV : {a : Set} {n : ℕ} → (_⊕_ : a → a → a) → (0' : a) → Vec a n → a
sumV {a} _⊕_  = foldr (λ _ → a) _⊕_



⨁ : {a : Set} → (plus : a → a → a) → (n : ℕ) → (aᵢ : ℕ → a) → a
⨁ _⊕_ zero aᵢ    = aᵢ 0
⨁ _⊕_ (suc n) aᵢ = ⨁ _⊕_ n aᵢ ⊕ aᵢ (suc n)

n-is-enough : {a : Set} -> ℕ → (plus : a -> a -> a) -> (gen : ℕ -> a) -> Set
n-is-enough n _⊕_ aᵢ = (m : ℕ) → ⨁ _⊕_ n aᵢ ≡ ⨁ _⊕_ (n + m) aᵢ

-- we don't have decidable equality and stuff, maybe, so I'm not sure if it is
-- possible to work with this, even if it sounds nice!
sum-is-finite : {a : Set} -> (plus : a -> a -> a) -> (gen : ℕ -> a) -> Set
sum-is-finite _⊕_ aᵢ = ∃ (λ n → n-is-enough n _⊕_ aᵢ)

valiant-sum-is-finite : ∀ {s} → Tri s → Set
valiant-sum-is-finite A = sum-is-finite _T+_ (λ n → A T^[1+ n ])

valiant-sum : ∀ {s} → (A : Tri s) → valiant-sum-is-finite A → Tri s
valiant-sum A (n , pf) = ⨁ _T+_ n (λ k → A T^[1+ k ])

has-transitive-closure : ∀ {s} → ℙ (Tri s)
has-transitive-closure = valiant-sum-is-finite 

corefl-has-transitive-closure : ∀ {s} → Tri s ← Tri s
corefl-has-transitive-closure = has-transitive-closure ¿


--_○_ : {i k : Level} {A : Set i} {B : Set}{C : Set k} → C ← B → B ← A → C ← A
--(R ○ S) c a = ∃ (λ b → S b a × R c b)
--_◍_ : {i k : Level} {A : Set i} {B : Set}{C : Set k} → C ← B → B ← A → C ← A
--(R ◍ S) c a = ∃ (λ b → Σ (S b a) (λ x → R c b))

-- check 
-- A⁺ A
transitiveclosure : ∀ {s} → Tri s ← Tri s
transitiveclosure {s} A⁺ A = ({!!} ○ corefl-has-transitive-closure) A⁺ A
-- sum-is-finite + 

valiant-der : {!!} 
valiant-der = {!!}