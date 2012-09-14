module Cata where

open import Data.Product
open import Data.Nat
open import Relation.Binary.PropositionalEquality

data List (a : Set) : Set where
  nil : List a
  cons : a -> List a -> List a

_++_ : ∀ {a} -> List a -> List a -> List a
nil ++ ys = ys
cons x xs ++ ys = cons x (xs ++ ys)


cataList : {a b : Set} -> (nil' : b) -> (cons' : a -> b -> b) -> List a -> b
cataList nil' cons' nil = nil'
cataList nil' cons' (cons x xs) = cons' x (cataList nil' cons' xs)

cut : ∀ {a} -> List a -> List a × List a
cut xs = {!!}

length : ∀ {a} -> List a -> ℕ 
length xs = cataList 0 (λ x x₁ → x₁ + 1) xs

data Bin (a : Set) : Set where
  nil : Bin a
  bin : Bin a -> a -> Bin a -> Bin a

cataBin : {a b : Set} -> (nil' : b) -> (bin' : b -> a -> b -> b) -> Bin a -> b
cataBin nil' bin' nil = nil'
cataBin nil' bin' (bin x x₁ x₂) = bin' (cataBin nil' bin' x) x₁ (cataBin nil' bin' x₂)


embed : ∀ {a} -> List a -> Bin a
embed nil = nil
embed (cons x xs) = bin nil x (embed xs)

proj : ∀ {a} -> Bin a -> List a
proj nil = nil
proj (bin xs x xs₁) = (proj xs) ++ (cons x (proj xs₁))

theorem : ∀ {a} -> (xs : List a) -> proj (embed xs) ≡ xs
theorem nil = refl
theorem (cons x xs) = cong (cons x) (theorem xs)


exercise : ∀ x y {nil' cons'} -> proj x ≡ proj y -> cataBin nil' cons' x ≡  cataBin nil' cons' y -- Assoc cons' !!!
exercise = {!!}

-- Do the whole thing again in 2 dimensions.


