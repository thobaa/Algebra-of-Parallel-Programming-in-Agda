module Cata where

open import Data.Product
open import Data.Nat
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Function


data List (a : Set) : Set where
  nil : List a
  cons : a -> List a -> List a

_++_ : {a : Set} -> List a -> List a -> List a
nil ++ ys = ys
(cons x xs) ++ ys = cons x (xs ++ ys)

++-assoc : {A : Set} (a b c : List A) → (a ++ b) ++ c ≡ a ++ (b ++ c)
++-assoc nil b c = refl
++-assoc (cons a as) b c = cong (cons a) (++-assoc as b c)

cataList : {a b : Set} -> (nil' : b) -> (cons' : a -> b -> b) -> List a -> b
cataList nil' cons' nil = nil'
cataList nil' cons' (cons x xs) = cons' x (cataList nil' cons' xs)

--cut : ∀ {a} -> List a -> List a × List a
--cut xs = {!!}

length : ∀ {a} -> List a -> ℕ 
length xs = cataList 0 (λ x x₁ → x₁ + 1) xs

data Bin (a : Set) : Set where
  empty : Bin a
  tip : a -> Bin a
  bin : Bin a -> Bin a -> Bin a

cataBin : {a b : Set} -> (empty' : b) -> (nil' : a -> b) -> (bin' : b -> b -> b) -> Bin a -> b
cataBin e' nil' bin' empty = e'
cataBin e' nil' bin' (tip x) = nil' x
cataBin e' nil' bin' (bin x₁ x₂) = bin' (cataBin e' nil' bin' x₁) (cataBin e' nil' bin' x₂)

embed : ∀ {a} -> List a -> Bin a
embed (nil) = empty
embed (cons x xs) = bin (tip x) (embed xs)

proj : ∀ {a} -> Bin a -> List a
proj empty = nil
proj (tip x) = cons x nil
proj (bin xs xs₁) = (proj xs) ++ (proj xs₁)

theorem : ∀ {a} -> (xs : List a) -> proj (embed xs) ≡ xs
theorem nil = refl
theorem (cons x xs) = cong (cons x) (theorem xs)



Associative : {A : Set} (f : A -> A -> A) -> Set
Associative f = ∀ x y z -> f (f x y) z ≡ f x (f y z)

lemma : ∀ {a b} {k : b} {f : a -> b -> b} x y -> cataList k f (x ++ y) ≡ cataList (cataList k f y) f x
lemma nil y = refl
lemma {f = f} (cons x x₁) y = cong (f x) (lemma x₁ y)

lemma' : ∀ {a b} {k : b} {i : a -> b} {_⊕_ : b -> b -> b} -> Associative _⊕_ -> (x y : List a) -> cataList k (_⊕_ ∘ i) (x ++ y) ≡ cataList k (_⊕_ ∘ i) x ⊕ cataList k (_⊕_ ∘ i) y
lemma' q nil y = {!k is left unit of _⊕_!}
lemma' q (cons x x₁) y = {!!}

exercise' : {a b : Set} {empty' : b} {sing' : a -> b} {bin' : b ->  b -> b} (x : Bin a) -> Associative bin' 
    -> cataBin empty' sing' bin' x ≡ cataList empty' (\a b -> bin' (sing' a) b) (proj x)
exercise' empty ass = refl
exercise' (tip x) ass = {!!}
exercise' (bin x x₁) ass = {!(1)!}


-- (1)
-- cataList .empty' (λ a → .bin' (.sing' a)) (proj x ++ proj x₁)
   -- cataList law
-- cataList .empty' (λ a → .bin' (.sing' a)) (proj x) `bin` cataList .empty' (λ a → .bin' (.sing' a)) (proj x₁)
   -- induction hyp
-- cataBin empty' sing' bin' x  `bin` cataBin empty' sing' bin' x



exercise : {a b : Set} {empty' : b} {sing' : a -> b} {bin' : b ->  b -> b} (x y : Bin a) -> 
  proj x ≡ proj y -> Associative bin' -> cataBin empty' sing' bin' x ≡ cataBin empty' sing' bin' y
exercise = {!!}


binFusion : {a b c : Set} -> (h : b -> c) -> (x : Bin a) -> {e : b}  {s : a -> b} {_⊕_ : b ->  b -> b} {_⊗_ : c ->  c -> c} -> (∀ a b -> h (a ⊕ b) ≡  h a ⊗ h b )
                          -> h (cataBin e s _⊕_ x) ≡ cataBin (h e) (h ∘ s) _⊗_ x
binFusion = ?

-- Do the whole thing again in 2 dimensions.


