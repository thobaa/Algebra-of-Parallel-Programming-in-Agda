module Matrix.Split where

open import Data.Nat
open import Data.Fin using (Fin; fromℕ; fromℕ≤; toℕ;  raise; reduce≥) 
                     renaming (zero to f0; suc to fsuc)

-- open import Data.Integer using (ℤ; +_; _-_)                        -- renaming (≥ to z≥)
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
  deeper : Splitting -> Splitting -> Splitting 



splitSize : Splitting -> ℕ
splitSize empty = 0
splitSize one = 1
splitSize (deeper s1 s2) = splitSize s1 + splitSize s2


data SplitMat (a : Set)  : Splitting -> Splitting → Set where
  one : (x : a) -> SplitMat a one one
  zero : ∀ {r c} -> SplitMat a r c -- either no extent, or zeros. => need ring
  quad : ∀ {r1 r2 c1 c2} -> (m11 : SplitMat a r1 c1) -> (m12 : SplitMat a r1 c2) -> 
                            (m21 : SplitMat a r2 c1) -> (m22 : SplitMat a r2 c2) 
          -> SplitMat a (deeper r1 r2) (deeper c1 c2)

data Triangle (a : Set) : Splitting → Set where
  one : Triangle a one
  quad : ∀ {s1 s2      } -> (m11 : Triangle a s1   ) -> (m12 : SplitMat a s1 s2) -> 
                                                        (m22 : Triangle a s2   ) 
          -> Triangle a (deeper s1 s2)


data Splitting' : ℕ -> Set where
  empty : ∀ {n} -> Splitting' n -- no extent
  one : Splitting' zero -- unsplittable
  deeper : ∀ {n} -> Splitting' n -> Splitting' n -> Splitting' (suc n)

forget : ∀ {n} -> Splitting' n -> Splitting
forget empty = empty
forget one = one
forget (deeper s s') = deeper (forget s) (forget s')

-- splitting of arbitrary depth of size 1.
cut1 : ∀ m -> ∃ \(s : Splitting' m) -> splitSize (forget s) ≡ 1
cut1 zero = one , refl
cut1 (suc m) with cut1 m 
... | r , q = deeper empty r , q

-- one can construct a splitting of arbitrary size if there is enough depth
cut : ∀ m n -> (m ≥ n) -> ∃ \(s : Splitting' m) -> splitSize (forget s) ≡ n
cut m .0 z≤n = empty , refl
cut .(suc n) .(suc m) (s≤s {m} {n} p) with cut n m p | cut1 n
... | s , q | s' , q' = (deeper s' s) , cong₂ _+_ q' q

split : ∀ {a} n (s1 s2 : Splitting' n) -> Matrix _ (splitSize (forget s1)) (splitSize (forget s2)) -> SplitMat a (forget s1) (forget s2) 
split _ empty _ m = zero
split _ _ empty m = zero
split zero one one m = one {!...!}
split (suc n) (deeper s1 s2) (deeper s3 s4) m = quad {!...!} {!!} {!!} {!!}
  
coerce : (T : ℕ -> ℕ -> Set) -> ∀ m n -> T m n -> ∃ \d -> ∃₂ \(s1 s2 : Splitting' d) -> T (splitSize (forget s1)) (splitSize (forget s2))
coerce T m n x with m ≤? n 
coerce T m n x | yes p with cut n m p | cut n n {!!} 
coerce T .(splitSize (forget proj₁)) n x | yes p | proj₁ , refl | proj₃ , proj₄ = _ , proj₁ , proj₃ , subst (T (splitSize (forget proj₁))) (sym proj₄) x
coerce T m n x | no ¬p with cut m n {!!} | cut m m {!!}
coerce T m .(splitSize (forget proj₁)) x | no ¬p | proj₁ , refl | proj₃ , proj₄ = _ , proj₃ , proj₁ , subst (\x -> T x (splitSize (forget proj₁))) (sym proj₄) x


_⊕_ : ∀ {a s1 s2} -> SplitMat a s1 s2 -> SplitMat a s1 s2 -> SplitMat a s1 s2
x ⊕ zero = {!x!}
zero ⊕ y = y
one x ⊕ one x₁ = one {!!}
quad x x₁ x₂ x₃ ⊕ quad y y₁ y₂ y₃ = quad (x ⊕ y) (x₁ ⊕ y₁) (x₂ ⊕ y₂) (x₃ ⊕ y₃)

_⊗_ : ∀ {a s1 s2 s3} -> SplitMat a s1 s2 -> SplitMat a s2 s3 -> SplitMat a s1 s3
x ⊗ zero = zero
zero ⊗ y = zero
one x ⊗ one y = one {!!}
quad x11 x12 x21 x22 ⊗ quad y11 y12 y21 y22 = 
  quad ((x11 ⊗ y11) ⊕ (x12 ⊗ y21)) ((x11 ⊗ y12) ⊕ (x12 ⊗ y22)) 
       ((x21 ⊗ y11) ⊕ (x22 ⊗ y21)) ((x21 ⊗ y12) ⊕ (x22 ⊗ y22)) -- TODO: this could generate more zeros


valiantOverlap : ∀ {a s1 s2} -> Triangle a s1 -> SplitMat a s1 s2 -> Triangle a s2 -> SplitMat a s1 s2
valiantOverlap A zero C = zero
valiantOverlap one (one x) one = one x
valiantOverlap (quad A1 A2 A3) (quad C2 C4 C1 C3) (quad B1 B2 B3) = quad X2 X4 X1 X3
  where X1 = valiantOverlap A3 C1 B1
        X2 = valiantOverlap A1 (C2 ⊕ (A2 ⊗ X1)) B1
        X3 = valiantOverlap A3 (C3 ⊕ (X1 ⊗ B2)) B3
        X4 = valiantOverlap A1 ((A2 ⊗ X3) ⊕ (X2 ⊗ B2)) B3

valiant : ∀ {a s} -> Triangle a s -> Triangle a s
valiant one = one
valiant (quad A C B) = quad A' (valiantOverlap A' C B') B'
  where A' = valiant A
        B' = valiant B



----------------------------------
-- seriously, this is ok! (vector with three elements
rowex : Splitting
rowex = (deeper (deeper one empty) (deeper empty empty))
colex : Splitting
colex = (deeper (deeper one one) (deeper one empty))

{-
exVec3 : (a : Ring') -> SplitMat _ rowex colex
-- r1 r2 c1 c2
exVec3 a = quad {a}{deeper one empty}{deeper empty empty}{deeper one one}{deeper one empty} 
                (quad (one (R1 a)) (one (R1 a)) empty empty)   
                (quad (one (R1 a)) empty empty empty) 
                empty 
                empty
-}
----------------------------------

