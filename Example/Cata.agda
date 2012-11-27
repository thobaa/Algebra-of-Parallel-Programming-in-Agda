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

LeftUnit : {A : Set} -> (_⊕_ : A -> A -> A) -> (e : A) -> Set
LeftUnit _⊕_ e  = ∀ ne -> e ⊕ ne ≡ ne

RightUnit : {A : Set} -> (_⊕_ : A -> A -> A) -> (e : A) -> Set
RightUnit _⊕_ e  = ∀ ne -> ne ⊕ e ≡ ne

Unit : {A : Set} -> (_⊕_ : A -> A -> A) -> (e : A) -> Set
Unit {A} _⊕_ e = ∀ (ne : A) ->  LeftUnit _⊕_ e × RightUnit _⊕_ e 

lemma : ∀ {a b} {k : b} {f : a -> b -> b} x y -> cataList k f (x ++ y) ≡ cataList (cataList k f y) f x
lemma nil y = refl
lemma {f = f} (cons x x₁) y = cong (f x) (lemma x₁ y)

-- erase the proof of cons and use C-c C-a!!! ☺
lemma' : ∀ {a b} {k : b} (i : a -> b) (_⊕_ : b -> b -> b) -> Associative _⊕_ -> LeftUnit _⊕_ k -> (x y : List a) -> cataList k (_⊕_ ∘ i) (x ++ y) ≡ cataList k (_⊕_ ∘ i) x ⊕ cataList k (_⊕_ ∘ i) y
lemma' {k = k} i _⊕_ as lu nil y = sym (lu (cataList k (λ z → _⊕_ (i z)) y))
lemma' {k = k} i _⊕_ as lu (cons x x₁) y = begin
       i x ⊕ cataList k (λ z → _⊕_ (i z)) (x₁ ++ y) 
           ≡⟨ cong (_⊕_ (i x)) (lemma' i _⊕_ as lu x₁ y) ⟩
       i x ⊕ (cataList k (λ z → _⊕_ (i z)) x₁ ⊕ cataList k (λ z → _⊕_ (i z)) y)
           ≡⟨ sym (as (i x) (cataList k (λ z → _⊕_ (i z)) x₁)
                            (cataList k (λ z → _⊕_ (i z)) y)) ⟩
       ((i x ⊕ cataList k (λ z → _⊕_ (i z)) x₁) ⊕ cataList k (λ z → _⊕_ (i z)) y
                                              ∎)

exercise' : {a b : Set} {empty' : b} {sing' : a -> b} {bin' : b ->  b -> b} (x : Bin a) -> Associative bin' -> Unit bin' empty'
    -> cataBin empty' sing' bin' x ≡ cataList empty' (\a b -> bin' (sing' a) b) (proj x)
exercise' empty ass unit = refl
exercise' {sing' = sing'} {bin' = bin'} (tip x) ass unit = sym (proj₂ (unit (bin' (sing' x) (sing' x))) (sing' x))
exercise' {a} {b} {empty'} {sing'} {bin'} (bin x x₁) ass unit = trans (lemma'' {a} {b} {empty'} {sing'} {bin'} x x₁ ass unit) (sym (lemma' sing' bin' ass (λ ne → proj₁ (unit ne) ne) (proj x) (proj x₁)))
  where 
  lemma'' : {a b : Set} {empty' : b} {sing' : a -> b} {bin' : b ->  b -> b} -> (x x₁ : Bin a) -> Associative bin' -> Unit bin' empty' ->
    cataBin empty' sing' bin' (bin x x₁) ≡ bin' (cataList empty' (λ a b -> bin' (sing' a) b) (proj x))  (cataList empty' (λ a b -> bin' (sing' a) b) (proj x₁))
  lemma'' {a} {b} {empty'} {sing'} {bin'} x x₁ pfac pfun = cong₂ bin' (exercise' x pfac pfun) (exercise' x₁ pfac pfun)



-- (1)
-- cataList .empty' (λ a → .bin' (.sing' a)) (proj x ++ proj x₁)
   -- cataList law
-- cataList .empty' (λ a → .bin' (.sing' a)) (proj x) `bin` cataList .empty' (λ a → .bin' (.sing' a)) (proj x₁)
   -- induction hyp
-- cataBin empty' sing' bin' x  `bin` cataBin empty' sing' bin' x

exercise : {a b : Set} {empty' : b} {sing' : a -> b} {bin' : b ->  b -> b} (x y : Bin a) -> 
  proj x ≡ proj y -> Associative bin' -> Unit bin' empty' -> cataBin empty' sing' bin' x ≡ cataBin empty' sing' bin' y
exercise {a} {b} {empty'} {sing'} {bin'}
  x y pxpy ass pfunit = begin cataBin empty' sing' bin' x
  ≡⟨ (exercise' {a} {b} {empty'} {sing'} {bin'} x ass pfunit) ⟩ 
  cataList empty' (λ z → bin' (sing' z)) (proj x)
  ≡⟨ cong (cataList empty' (λ z → bin' (sing' z))) pxpy ⟩
  cataList empty' (λ z → bin' (sing' z)) (proj y)
  ≡⟨ sym (exercise' {a} {b} {empty'} {sing'} {bin'} y ass pfunit) ⟩
  cataBin empty' sing' bin' y
  ∎

binFusion : {a b c : Set} -> (h : b -> c) -> (x : Bin a) -> {e : b}  {s : a -> b} {_⊕_ : b ->  b -> b} {_⊗_ : c ->  c -> c} -> (∀ a b -> h (a ⊕ b) ≡  h a ⊗ h b )
                          -> h (cataBin e s _⊕_ x) ≡ cataBin (h e) (h ∘ s) _⊗_ x
binFusion h empty      ha+b≡ha*hb = refl
binFusion h (tip y)    ha+b≡ha*hb = refl
binFusion h (bin y y') {e} {s} {_⊕_} {_⊗_} ha+b≡ha*hb = begin 
  h ((cataBin e s _⊕_ y) ⊕ (cataBin e s _⊕_ y')) 
     ≡⟨ ha+b≡ha*hb (cataBin e s _⊕_ y) (cataBin e s _⊕_ y') ⟩
  h (cataBin e s _⊕_ y) ⊗ h (cataBin e s _⊕_ y')
    ≡⟨ cong₂ _⊗_ (binFusion h y ha+b≡ha*hb) (binFusion h y' ha+b≡ha*hb) ⟩
  cataBin (h e) (λ z → h (s z)) _⊗_ y ⊗
    cataBin (h e) (λ z → h (s z)) _⊗_ y' ∎


-- Functor laws:
mapBin : {a b : Set} -> (a -> b) -> (Bin a -> Bin b)
mapBin f empty = empty
mapBin f (tip y) = tip (f y)
mapBin f (bin y y') = bin (mapBin f y) (mapBin f y')

-- id:
data identity {a : Set} (f : a -> a) : Set where
  Id : (∀ x -> f x ≡ x) -> identity f

-- respects identity:
bin-id : ∀ {a} -> (id : a -> a) -> (identity id) -> (identity (mapBin id))
bin-id {a} id (Id pf) = Id (helper)
  where
  helper : (x : Bin a) → mapBin id x ≡ x 
  helper empty = refl
  helper (tip y) = cong tip (pf y)
  helper (bin y y') = cong₂ bin (helper y) (helper y')

-- respects composition:
bin-comp : ∀ {a b c x} -> (f : a -> b) -> (g : b -> c) -> (mapBin (g ∘ f)) x ≡ ((mapBin g) ∘ (mapBin f)) x
bin-comp {a} {b} {c} {empty} f g = refl
bin-comp {a} {b} {c} {tip y} f g = refl
bin-comp {a} {b} {c} {bin y y'} f g = cong₂ bin (bin-comp f g) (bin-comp f g)

-- Do the whole thing again in 2 dimensions.




--------------------------------------------------------------------------
--- Messy below!
--------------------------------------------------------------------------

-- quad:     n           p
--       -----------------------
--       |         |           |
--     m |  m x n  |   m x p   |
--       -----------------------
--     q |  q x n  |   q x p   |
--       -----------------------
-- 
-- 
--

{-

data Matrix2n (a : Set) : ℕ -> Set where
  zero : ∀ n -> Matrix2n a n
  sing : a -> Matrix2n a 0
  4x   : ∀ {n} -> Matrix2n a n -> Matrix2n a n -> 
                  Matrix2n a n -> Matrix2n a n ->
                  Matrix2n a (suc n)
       


open import Data.Vec renaming (_++_ to _++v_)

-- m columns, each of height n
data Matrix (a : Set) : (m n : ℕ) -> Set where
  colMat : ∀ {m} {n} -> Vec (Vec a (suc m)) (suc n) -> Matrix a m n

matrix : (a : Set) (m n : ℕ) -> Set
matrix a m n = Vec (Vec a (suc m)) (suc n)

data TMatrix (a : Set) : (m n : ℕ) -> Set where
  Tsing : a -> TMatrix a 0 0
  Tleft : ∀ {m n p} -> TMatrix a m n -> TMatrix a m p -> TMatrix a m (suc (n + p))
  Tover : ∀ {m n p} -> TMatrix a m n -> TMatrix a p n -> TMatrix a (suc (m + p)) n

embedVec : ∀ {a n} -> Vec a (suc n) -> TMatrix a n 0
embedVec {a} {zero} (x ∷ []) = Tsing x
embedVec {a} {suc n} (x ∷ xs) = Tover (Tsing x) (embedVec xs)

embedMat : ∀ {a m n} -> Matrix a m n -> TMatrix a m n
--embedMat (colMat ) = {!!}
embedMat {a} {m} {zero} (colMat (x ∷ [])) = embedVec x
embedMat {a} {m} {suc n} (colMat (x ∷ xs)) = Tleft (embedVec x) (embedMat (colMat xs)) --Tleft {!embedVec x!} {!!}

embedmat : ∀ {a m n} -> matrix a m n -> TMatrix a m n 
embedmat {a} {m} {zero} (x ∷ []) = embedVec x
embedmat {a} {m} {suc n} (x ∷ xs) = Tleft (embedVec x) (embedmat xs)


veceq : ∀ {a : Set} (n m : ℕ) -> Vec a (n + m) -> Vec a (m + n)
veceq zero .0 [] = []
veceq zero .(suc n) (_∷_ {n} x xs) = x ∷ veceq zero n xs
veceq (suc n) zero (x ∷ xs) = x ∷ veceq n zero xs
veceq {a} (suc n) (suc n') (x ∷ xs) = x ∷ veceq (suc n) n' (lemma1 a n n' xs) 
  where
  lemma1 : ∀ a n n' -> Vec a (n + suc n') -> Vec a (suc n + n')
  lemma1 a' zero m v = v
  lemma1 a' (suc n0) m (x' ∷ xs') = x' ∷ lemma1 a' n0 m xs'




--Goal: Vec .a (n' + suc n)
projmat : ∀ {a m n} -> TMatrix a m n -> matrix a m n
projmat (Tsing y) = (y ∷ []) ∷ []
projmat (Tleft y y') = lemma0 (projmat y ++v projmat y')
  where
  lemma0 : ∀ {a : Set} {m n p : ℕ} -> Vec (Vec a (suc m)) (suc (n + suc p)) → Vec (Vec a (suc m)) (suc (suc (n + p)))
  lemma0 {a} {m} {zero} {p} vs = vs
  lemma0 {a} {m} {suc n} {p} (x ∷ xs) = x ∷ lemma0 {a} {m} {n} {p} xs
projmat (Tover y y') = {!!}
--projmat {a} {m} {n} (Tleft y y') =-- veceq {!m n!} {!!} (projmat y ⊹⊹ projmat y')

-- TODO:
-- embed
-- proj
-- proj embed == id 
-- cataMat
-- cataTMat
--    exercise (proj x == proj y => cataTMat x == cataTMat y)
--    fusion
-- functor

-}