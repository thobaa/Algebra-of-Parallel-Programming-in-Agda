module NewSplit where

open import Data.Nat
open import Data.Fin using (Fin; fromℕ; fromℕ≤; toℕ;  raise; reduce≥) 
                     renaming (zero to f0; suc to fsuc)

open import Data.Integer using (ℤ; +_; _-_)
                        -- renaming (≥ to z≥)
open import Data.Vec renaming (Vec to SVec; [_] to <_>)
open import Matrix.Definitions using (toℤ) renaming (_≥_ to _z≥_; _<_ to _z<_)
open import Data.Empty
open import Algebra
open import Algebra.Structures
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Function
open import Relation.Nullary.Core

open import Relation.Binary.HeterogeneousEquality using (_≅_; ≡-to-≅)
open Relation.Binary.HeterogeneousEquality.≅-Reasoning



open import Matrix.Abstract

-- ones contain a size!
data Splitting : Set where
--  one : Splitting
  nosplit : ℕ -> Splitting
  deeper  : Splitting -> Splitting -> Splitting


one = nosplit 1

splitSize : Splitting -> ℕ
--splitSize one = 1 
splitSize (nosplit n) = n
splitSize (deeper s1 s2) = splitSize s1 + splitSize s2

-- ska inte vara nosplit, ska vara split hursomhelst!
-- för en vektor ------------ ska kunna ersätta en ----------|--------- (eller ????)
data SplitMat (a : Ring') : Splitting -> Splitting -> Set where
  RVec : {n : ℕ} -> Vec a (suc n) -> SplitMat a (nosplit 1) (nosplit (suc n))
  CVec : {n : ℕ} -> Vec a (suc n) -> SplitMat a (nosplit (suc n)) (nosplit 1)
  quad : ∀ {r1 r2 c1 c2} -> (A₁₁ : SplitMat a r1 c1) -> (A₁₂ : SplitMat a r1 c2) ->
                            (A₂₁ : SplitMat a r2 c1) -> (A₂₂ : SplitMat a r2 c2)  
         -> SplitMat a (deeper r1 r2) (deeper c1 c2)

splitToMat : ∀ a {rs cs} -> SplitMat a rs cs -> Matrix a (splitSize rs) (splitSize cs)
splitToMat a s = {!!}

-- uppdelning för första givet att andra är
-- |-|----
-- |-|----
-- | | 
-- | | 
simpleSplit : ℕ -> ℕ -> Splitting
simpleSplit zero n = nosplit 0
simpleSplit (suc n) zero = nosplit 0
simpleSplit 1 1 = nosplit 1
simpleSplit (suc (suc m)) 1 = nosplit (suc (suc m))
simpleSplit (suc m) (suc (suc n)) = deeper (nosplit (suc m)) (simpleSplit m (suc (suc n)))
{-
simpleSplit : ℕ -> ℕ -> Splitting
simpleSplit zero n = nosplit 0
simpleSplit (suc m) zero = nosplit 0
simpleSplit (suc zero) (suc zero) = one
simpleSplit (suc (suc n)) (suc zero) = nosplit n
simpleSplit (suc m) (suc (suc n)) = deeper one (simpleSplit m (suc n))
-}
{-
splitsize∘simpleSplit≡id : (n : ℕ) -> splitSize (simpleSplit n) ≡ n
splitsize∘simpleSplit≡id zero = refl
splitsize∘simpleSplit≡id (suc zero) = refl
splitsize∘simpleSplit≡id (suc (suc n)) = cong suc (splitsize∘simpleSplit≡id (suc n)) -- cong suc (splitsize∘simpleSplit≡suc n)
-}
----------------------------------
-- seriously, this is not ok! (vector with three elements
rowex : Splitting
rowex = nosplit 1
colex : Splitting
colex = nosplit 3

exVec3 : (a : Ring') -> SplitMat a rowex colex
-- r1 r2 c1 c2
exVec3 a = RVec (λ _ → R1 a) --R1 a ∷ R1 a ∷ R1 a ∷ [])
----------------------------------











-- ?
{-
split : ℕ -> ℕ -> Splitting
split zero zero = one
split zero (suc n) = nosplit (suc (suc n))
split (suc n) zero = nosplit (suc (suc n))
split (suc n) (suc n') = deeper {!!} {!!}-}

-- split tar 2 tal
split' : ℕ -> ℕ -> Splitting × Splitting
split' zero zero = nosplit 1 , nosplit 1
split' zero (suc n) = nosplit 1 , nosplit (suc (suc n))
split' (suc n) zero = nosplit (suc (suc n)) , nosplit 1
split' (suc n) (suc n') = deeper (nosplit 1) (proj₁ rec) , deeper (nosplit 1) (proj₂ rec) where rec = split' n n'

split'' : ℕ -> ℕ -> Splitting
split'' zero n = nosplit 1
split'' (suc n) zero = nosplit (suc (suc n))
split'' (suc n) (suc n') = deeper (nosplit 1) (split'' n n')
--RVecToSplit : ∀ {a n} -> Vec a (suc n) -> SplitMat a one (nosplit (suc n))
--RVecToSplit {a} {zero} v = sing (v f0) --sing (v f0)
--RVecToSplit {a} {suc n} v = RVec v
{-
CVecToSplit : ∀ {a n} -> Vec a (suc n) -> SplitMat a (split 0 n) one
CVecToSplit {a} {zero} v = sing (v f0)
CVecToSplit {a} {suc n} v = CVec v -}
-- Goal: SplitMat a one (simpleSplit (suc n) (suc m)) ska vara en vektor dvs simplesplit ? nosplit suc n
-- Goal: SplitMat a (simpleSplit (suc m) (suc n)) one ska vara 
RToSplit : ∀ {a n} -> (s : Splitting) -> Vec a (suc n) -> SplitMat a (nosplit 1) s
RToSplit s = {!!}
matToSplit : ∀ a {m n} -> Matrix a (suc m) (suc n) -> SplitMat a (proj₁ (split' m n)) (proj₂ (split' m n))
matToSplit a {zero} {zero} A = RVec (λ x → A x x)
matToSplit a {zero} {suc n} A = RVec (λ x → A f0 x)
matToSplit a {suc n} {zero} A = CVec (λ x → A x f0) -- CVec (λ x → A (fsuc x) f0) -- hmm
matToSplit a {suc m} {suc n} A with split' m n 
matToSplit a {suc m} {suc n} A | nosplit y , proj₂ = {!!}
matToSplit a {suc m} {suc n} A | deeper y y' , proj₂ = {!y!} --quad (RVec (λ x → A f0 f0) ) ?
             --                         {!!}                    (matToSplit a (λ i j → A (fsuc i) (fsuc j))) --quad (sing (A f0 f0)) (RToSplit (λ x → A {!!} {!!})) {!!} (matToSplit a {m} {n} (λ i j → A (fsuc i) (fsuc j)))

matToSplit' : ∀ a {m n} -> Matrix a (suc m) (suc n) -> SplitMat a (split'' m n) (split'' n m)
matToSplit' a {zero} {zero} A = RVec (λ x → A x x)
matToSplit' a {zero} {suc n} A = RVec (λ x → A f0 x)
matToSplit' a {suc n} {zero} A = CVec (λ x → A x f0) -- CVec (λ x → A (fsuc x) f0) -- hmm
matToSplit' a {suc m} {suc n} A = quad (RVec (λ x → A f0 f0) ) {!!}
                                       {!!}                     (matToSplit' a (λ i j → A (fsuc i) (fsuc j))) --quad (sing (A f0 f0)) (RToSplit (λ x → A {!!} {!!})) {!!} (matToSplit a {m} {n} (λ i j → A (fsuc i) (fsuc j)))


-- (RVecToSplit {a} {n} (λ x → A f0 (fsuc x))) (CVecToSplit {a} {m} (λ x → A (fsuc x) f0)) (matToSplit a {m} {n} (λ i j → A (fsuc i) (fsuc j)))
--quad (one (A f0 f0)) (RVectoSplit (λ x → A f0 (fsuc x))) (CVectoSplit (λ x → A (fsuc x) f0)) (matToSplit a (λ i j → A (fsuc i) (fsuc j)))

{-matToMat≡Id : ∀ a m n -> (A : Matrix a m n) -> splitToMat a (matToSplit a A) ≅ A
matToMat≡Id a zero n A = begin 
                               splitToMat a (matToSplit a A) 
                                 ≅⟨ {!Extensionality ? ?!} ⟩ -- or applying
                               A ∎
matToMat≡Id a m n A = {!!}
-}{-
fromSplitted : ∀ n -> Fin (splitSize (simpleSplit n)) → Fin n
fromSplitted n fn = {!!}
-}

-- cong4
{-
matToMat≡Id' : ∀ a m n i j -> (A : Matrix a m n) -> splitToMat a (matToSplit a A) i j ≅ A (fromSplitted m i) (fromSplitted n j) 
matToMat≡Id' a m n i j A  = {!!} {-with matToSplit a A -}
matToMat≡Id' a zero n () j A | empty
matToMat≡Id' a (suc n) zero i () A | empty
matToMat≡Id' a (suc n) (suc n') i j A | empty = {!!}
matToMat≡Id' a (suc n) (suc n') i j A | quad m11 m12 m21 m22 = {!!}-}
 {-zero n () j A
matToMat≡Id' a (suc n) zero i () A
matToMat≡Id' a (suc n) (suc n') f0 f0 A = {!!}
matToMat≡Id' a (suc n) (suc n') f0 (fsuc i) A = {!!}
matToMat≡Id' a (suc n) (suc n') (fsuc i) f0 A = {!!}
matToMat≡Id' a (suc n) (suc n') (fsuc i) (fsuc i') A = matToMat≡Id' a n n' i i' (λ x y → A (fsuc x) (fsuc y))-}