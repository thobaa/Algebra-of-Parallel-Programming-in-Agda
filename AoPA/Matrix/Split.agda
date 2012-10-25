module Matrix.Split where

open import Data.Nat
open import Data.Fin using (Fin; fromℕ; fromℕ≤; toℕ;  raise; reduce≥) 
                     renaming (zero to f0; suc to fsuc)

open import Data.Integer using (ℤ; +_; _-_)
                        -- renaming (≥ to z≥)
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



data Splitting : Set where
  empty : Splitting -- no extent
  one : Splitting -- unsplittable
  deeper : Splitting -> Splitting -> Splitting -- what does pos do here?



splitSize : Splitting -> ℕ
splitSize empty = 0
splitSize one = 1
splitSize (deeper s1 s2) = splitSize s1 + splitSize s2


-- does this really allow all kinds of matrices???
-- all matrixes must!!! have the same split structure for rows and cols.
data SplitMat (a : Ring') : Splitting -> Splitting → Set where
  one : (x : RC a) -> SplitMat a one one
  empty : ∀ {r c} -> SplitMat a r c -- either no extent, or zeros. => need ring
  quad : ∀ {r1 r2 c1 c2} -> (m11 : SplitMat a r1 c1) -> (m12 : SplitMat a r1 c2) -> 
                            (m21 : SplitMat a r2 c1) -> (m22 : SplitMat a r2 c2) 
          -> SplitMat a (deeper r1 r2) (deeper c1 c2)

quadMat : ∀ {a r1 r2 c1 c2} -> Matrix a r1 c1 -> Matrix a r1 c2 ->
                               Matrix a r2 c1 -> Matrix a r2 c2 -> 
                               Matrix a (r1 + r2) (c1 + c2)
quadMat A B 
        C D i j = {!!}

splitToMat : ∀ a {rs cs} -> SplitMat a rs cs -> Matrix a (splitSize rs) (splitSize cs)
splitToMat a (one x) = λ i j → x
splitToMat a (empty {rs} {cs}) = λ i j → R0 a
splitToMat a (quad A B 
                 C D) = λ i j → {!!}

-- måste vara såhär, för 
simpleSplit : ℕ -> Splitting
simpleSplit zero = empty
simpleSplit (suc n) = deeper one (simpleSplit n)

splitsize∘simpleSplit≡suc : (n : ℕ) -> splitSize (simpleSplit n) ≡ n
splitsize∘simpleSplit≡suc zero = refl
splitsize∘simpleSplit≡suc (suc n) = cong suc (splitsize∘simpleSplit≡suc n)

----------------------------------
-- seriously, this is not ok! (vector with three elements
rowex : Splitting
rowex = (deeper (deeper one empty) (deeper empty empty))
colex : Splitting
colex = (deeper (deeper one one) (deeper one empty))

exVec3 : (a : Ring') -> SplitMat a rowex colex
-- r1 r2 c1 c2
exVec3 a = quad {a}{deeper one empty}{deeper empty empty}{deeper one one}{deeper one empty} 
                (quad (one (R1 a)) (one (R1 a)) empty empty)   
                (quad (one (R1 a)) empty empty empty) 
                empty 
                empty
----------------------------------

RVectoSplit : ∀ {a n} -> Vec a n -> SplitMat a one (simpleSplit n)
RVectoSplit {a} {zero} v = empty
RVectoSplit {a} {suc n} v = {!!}

CVectoSplit : ∀ {a n} -> Vec a n -> SplitMat a (simpleSplit n) one
CVectoSplit v = {!!} 

matToSplit : ∀ a {m n} -> Matrix a m n -> SplitMat a (simpleSplit m) (simpleSplit n)
matToSplit a {zero} {n} A = empty
matToSplit a {suc n} {zero} A = empty
matToSplit a {suc m} {suc n} A = quad (one (A f0 f0)) {!matToSplit!} {!!} {!!}

--quad (one (A f0 f0)) (RVectoSplit (λ x → A f0 (fsuc x))) (CVectoSplit (λ x → A (fsuc x) f0)) (matToSplit a (λ i j → A (fsuc i) (fsuc j)))

matToMat≡Id : ∀ a m n -> (A : Matrix a m n) -> splitToMat a (matToSplit a A) ≅ A
matToMat≡Id a zero n A = begin 
                               splitToMat a (matToSplit a A) 
                                 ≅⟨ {!Extensionality ? ?!} ⟩ -- or applying
                               A ∎
matToMat≡Id a m n A = {!!}

fromSplitted : ∀ n -> Fin (splitSize (simpleSplit n)) → Fin n
fromSplitted zero ()
fromSplitted (suc n) f0 = f0
fromSplitted (suc n) (fsuc i) = fsuc (fromSplitted n i)


-- cong4

matToMat≡Id' : ∀ a m n i j -> (A : Matrix a m n) -> splitToMat a (matToSplit a A) i j ≅ A (fromSplitted m i) (fromSplitted n j) 
matToMat≡Id' a m n i j A with matToSplit a A 
matToMat≡Id' a zero n () j A | empty
matToMat≡Id' a (suc n) zero i () A | empty
matToMat≡Id' a (suc n) (suc n') i j A | empty = {!!}
matToMat≡Id' a (suc n) (suc n') i j A | quad m11 m12 m21 m22 = {!!}
 {-zero n () j A
matToMat≡Id' a (suc n) zero i () A
matToMat≡Id' a (suc n) (suc n') f0 f0 A = {!!}
matToMat≡Id' a (suc n) (suc n') f0 (fsuc i) A = {!!}
matToMat≡Id' a (suc n) (suc n') (fsuc i) f0 A = {!!}
matToMat≡Id' a (suc n) (suc n') (fsuc i) (fsuc i') A = matToMat≡Id' a n n' i i' (λ x y → A (fsuc x) (fsuc y))-}