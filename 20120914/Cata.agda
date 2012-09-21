module Cata where

open import Data.Product
open import Data.Nat
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import Data.Nat.Properties
open import Algebra using (CommutativeSemiring)
open Algebra.CommutativeSemiring commutativeSemiring using (+-comm; +-assoc;
                                                            +-identity)
open import Induction.Nat renaming (<-well-founded to <ℕ-wf)
open Data.Nat.≤-Reasoning using (_≤⟨_⟩_) 
                          renaming (begin_ to ≤begin_; _∎ to_≤∎; 
                                    _≡⟨_⟩_ to _≤≡⟨_⟩_)

open import Data.Sum
open import Induction
open import Induction.WellFounded
open import Algebra.RingSolver.AlmostCommutativeRing

open SemiringSolver


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

length : ∀ {a} -> List a -> ℕ 
length xs = cataList 0 (λ x x₁ → x₁ + 1) xs

data Bin (a : Set) : Set where
  tip : Bin a
  bin : Bin a -> a -> Bin a -> Bin a

cataBin : {a b : Set} -> (nil' : b) -> (bin' : b -> a -> b -> b) -> Bin a -> b
cataBin nil' bin' tip = nil'
cataBin nil' bin' (bin x x₁ x₂) = bin' (cataBin nil' bin' x) x₁ 
                                       (cataBin nil' bin' x₂)


embed : ∀ {a} -> List a -> Bin a
embed nil = tip
embed (cons x xs) = bin tip x (embed xs)

proj : ∀ {a} -> Bin a -> List a
proj tip = nil
proj (bin xs x xs₁) = (proj xs) ++ (cons x (proj xs₁))

theorem : ∀ {a} -> (xs : List a) -> proj (embed xs) ≡ xs
theorem nil = refl
theorem (cons x xs) = cong (cons x) (theorem xs)


data associative {A B : Set} (f : B -> A -> B -> B) : Set where
  assoc : (∀ x a y b z -> f (f x a y) b z ≡ f x a (f y b z)) -> associative f

cons≢nil : {a : Set} {x : a} {xs : List a} -> cons x xs ≢ nil
cons≢nil = λ ()

-- proj x == nil => x = refl
++cons≢nil : {a : Set} {xs : List a} {y : a} {ys : List a} -> 
             (xs ++ cons y ys) ≢ nil
++cons≢nil {a} {xs} {y} {ys} x = lemma xs (cons y ys) (cons≢nil {a} {y} {ys}) x
  where 
    lemma : {a : Set} (xs : List a) (ys : List a) -> ys ≢ nil -> xs ++ ys ≢ nil
    lemma xs          nil          pf x = pf refl
    lemma nil         (cons y y')  pf x = pf x
    lemma (cons y y') (cons y0 y1) pf ()

pf : {a : Set} {x : Bin a} -> proj x ≡ nil -> x ≡ tip
pf {_} {tip} px≡nil = refl
pf {a} {bin y y' y0} px≡nil = ⊥-elim (++cons≢nil {a} {proj y} {_} {_} px≡nil) 

pf' : ∀ {X} {x : Bin X} -> x ≡ tip -> proj x ≡ nil
pf' {_} {tip} x≡tip = refl
pf' {_} {bin y y' y0} ()

cong₃ : {X Y Z W : Set} {x1 x2 : X} {y1 y2 : Y} {z1 z2 : Z}
  (f : X → Y → Z → W) → x1 ≡ x2 -> y1 ≡ y2 -> z1 ≡ z2 -> f x1 y1 z1 ≡ f x2 y2 z2
cong₃ {_} {_} {_} {_} {x1} {x2} {y1} {y2} {z1} {z2} f pfx pfy pfz = begin 
  f x1 y1 z1 ≡⟨ cong₂ (λ y0 z0 → f x1 y0 z0) pfy pfz ⟩
  f x1 y2 z2 ≡⟨ cong  (λ z0    → f z0 y2 z2) pfx     ⟩
  f x2 y2 z2 ∎

conslemma1 : ∀ {a} {x y : a} {xs ys : List a} -> 
             cons x xs ≡ cons y ys -> xs ≡ ys
conslemma1 refl = refl

conslemma2 : ∀ {A} {x y : A} {xs ys : List A} -> 
             cons x xs ≡ cons y ys -> x ≡ y
conslemma2 refl = refl

++lemma1 : ∀ {A} {xs ys : List A} {x y : A} -> 
           xs ++ (cons x nil) ≡ ys ++ (cons y nil) -> xs ≡ ys
++lemma1 {A} {nil} {nil} refl = refl 
++lemma1 {A} {nil} {cons c cs} {x} {y} pf = 
  ⊥-elim (++cons≢nil {A} {cs} {y} {nil} (sym (conslemma1 {A} {x} {c} pf)))
++lemma1 {A} {cons b bs} {nil} {x} {y} pf = 
  ⊥-elim (++cons≢nil {A} {bs} {x} {nil} (conslemma1 {A} {b} {y} pf))
++lemma1 {A} {cons b bs} {cons c cs} {x} {y} pf = cong₂ (λ x' xs → cons x' xs) 
                   (conslemma2 pf) (++lemma1 {A} {bs} {cs} {x} {y} 
                   (conslemma1 pf))

++lemma2 : ∀ {A} {xs ys : List A} {x y : A} -> 
           xs ++ (cons x nil) ≡ ys ++ (cons y nil) -> x ≡ y 
++lemma2 {A} {nil} {nil} refl = refl 
++lemma2 {A} {nil} {cons c cs} {x} {y} pf =
  ⊥-elim (++cons≢nil {A} {cs} {y} {nil} (sym (conslemma1 {A} {x} {c} pf)))
++lemma2 {A} {cons b bs} {nil} {x} {y} pf = 
  ⊥-elim (++cons≢nil {A} {bs} {x} {nil} (conslemma1 {A} {b} {y} pf))
++lemma2 {A} {cons b bs} {cons c cs} {x} {y} pf = 
  ++lemma2 {A} {bs} {cs} {x} {y} (conslemma1 pf)




size : {a : Set} -> Bin a -> ℕ
size tip = 0
size (bin y y' y0) = 2 * size y + size y0 + 1

data _<T_ {a : Set} : Bin a -> Bin a -> Set where
  <T-intr : ∀ {t1 t2} -> size t1 <′ size t2 -> t1 <T t2

x≮Ttip : {a : Set} {x : Bin a} -> x <T tip  -> ⊥
x≮Ttip (<T-intr ())

unsize : ∀ {a} {x y : Bin a} -> x <T y -> size x <′ size y
unsize (<T-intr y') = y'
 
-- from internet!
ii-acc : ∀ {a x} -> Acc _<′_ (size {a} x) -> Acc _<T_ x
ii-acc (acc rs) = acc (λ y x → ii-acc (rs (size y) (unsize x)))

ii-wf : {a : Set} -> Well-founded _<′_ -> Well-founded (_<T_ {a})
ii-wf wf x = ii-acc (wf (size x))




<T-wf : {a : Set} -> Well-founded (_<T_ {a})
<T-wf = ii-wf <ℕ-wf

bin-lemma : {a : Set} {y1 : Bin a} {x : a} -> y1 <T bin tip x y1
bin-lemma {a} {y} {x} = <T-intr (≤⇒≤′ (
  ≤begin 
  suc (size y) ≤≡⟨ +-comm (suc zero) (size y) ⟩ 
  size y + suc zero ≤∎))

binbin-lemma : {a : Set} {t1 t2 t3 : Bin a} {x1 x2 : a} -> 
               (bin t1 x1 (bin t2 x2 t3)) <T (bin (bin t1 x1 t2) x2 t3)
binbin-lemma {a} {t1} {t2} {t3} {x1} {x2} = <T-intr (≤⇒≤′ (
  ≤begin 

  1 + (size t1 + (size t1 + 0) + (size t2 + (size t2 + 0) + size t3 + 1) + 1)

  ≤≡⟨ solve 3 (λ x y z → 
     con 1 :+ (x :+ (x :+ con 0) :+ (y :+ (y :+ con 0) :+ z :+ con 1) :+ con 1)
     :=
     x :+ x :+ y :+ y :+ z :+ con 1 :+ con 1 :+ con 1)
      refl (size t1) (size t2) (size t3) ⟩ 

  size t1 + size t1 + size t2 + size t2 + size t3 + 1 + 1 + 1

    ≤⟨ actual-proof ⟩

  size t1 + size t1 + size t2 + size t1 + size t1 + size t2 + size t3 + 
    1 + 1 + 1

    ≤≡⟨ solve 3 (λ x y z → 
      x :+ x :+ y :+ x :+ x :+ y :+ z :+ con 1 :+ con 1 :+ con 1 
      := 
      x :+ (x :+ con 0) :+ y :+ con 1 :+ (x :+ (x :+ con 0) :+ y :+ con 1 :+ 
        con 0) :+ z :+ con 1) 
        refl (size t1) (size t2) (size t3) ⟩ 

  size t1 + (size t1 + 0) + size t2 + 1 + (size t1 + (size t1 + 0)
  + size t2 + 1 + 0) + size t3 + 1 ≤∎))
  where 
    m≤m : (a : ℕ) -> a ≤ a
    m≤m zero = z≤n
    m≤m (suc n) = s≤s (m≤m n)
    lemma1 : size t1 + size t1 + size t2 ≤ size t1 + size t1 + size t2 + 
             size t1 + size t1
    lemma1 = 
      ≤begin 
       size t1 + size t1 + size t2 
      ≤≡⟨ trans (sym (proj₂ +-identity (size t1 + size t1 + size t2))) 
                (sym (proj₂ +-identity (size t1 + size t1 + size t2 + 0))) ⟩
 
       size t1 + size t1 + size t2 + 0 + 0 

      ≤⟨      (((m≤m (size t1) 
         +-mono (m≤m (size t1))) 
         +-mono (m≤m (size t2))) 
         +-mono  z≤n) 
         +-mono  z≤n ⟩ 
       size t1 + size t1 + size t2 + size t1 + size t1
      ≤∎

    actual-proof :  size t1 + size t1 + size t2 + size t2 + size t3 + 1 + 1 + 1 
                    ≤ size t1 + size t1 + size t2 + size t1 + size t1 + size t2
                    + size t3 + 1 + 1 + 1
    actual-proof = ((((lemma1
      +-mono (m≤m (size t2))) 
      +-mono (m≤m (size t3))) 
      +-mono (m≤m (suc zero))) 
      +-mono (m≤m (suc zero))) 
      +-mono  m≤m (suc zero)

exercise : {a b : Set} {nil' : b} {cons' : b -> a -> b -> b} (x y : Bin a) -> 
  proj x ≡ proj y -> associative cons' -> 
  cataBin nil' cons' x ≡  cataBin nil' cons' y -- Assoc cons' !!!
-- tip tip
exercise {a} {b} {nil'} {cons'} t s pxpy ac =  
         helper nil' cons' t s pxpy ac (<T-wf t) (<T-wf s)
  where
    helper :  {a b : Set} (nil' : b) (cons' : b -> a -> b -> b) (x y : Bin a) ->
      proj x ≡ proj y -> associative cons' ->  Acc _<T_ x -> Acc _<T_ y -> 
      cataBin nil' cons' x ≡  cataBin nil' cons' y
    helper _ _ tip tip pf ac' _ _ = refl
    helper _ _ tip (bin y y' y0) pf ac' _ _ = 
      ⊥-elim (++cons≢nil {_} {proj y} (sym pf))
    helper _ _ (bin y y' y0) tip pf ac' _ _ = 
      ⊥-elim (++cons≢nil {_} {proj y} pf)
    helper nil' cons' (bin tip y' y0) 
                      (bin tip y2 y3) pf ac' (acc funx) (acc funy) = cong₂ 
           (λ x x' → cons' nil' x x') (conslemma2 pf) 
           (helper nil' cons' y0 y3 (conslemma1 pf) ac' (funx y0 bin-lemma) 
                                                        (funy y3 bin-lemma))
    helper nil' cons' (bin tip y' y0) 
                      (bin (bin y y1 y2) y3 y4) 
           pf (assoc pfac) (acc funx) (acc funy) = begin 
      cons' nil' y' (cataBin nil' cons' y0) 
        ≡⟨ helper nil' cons' (bin tip y' y0) 
                             (bin y y1 (bin y2 y3 y4)) 
                  (trans pf (++-assoc (proj y) (cons y1 (proj y2)) 
                                               (cons y3 (proj y4)))) 
                  (assoc pfac) (acc funx) 
                               (funy (bin y y1 (bin y2 y3 y4)) binbin-lemma) ⟩ 
      cons' (cataBin nil' cons' y) y1
            (cons' (cataBin nil' cons' y2) y3 (cataBin nil' cons' y4)) 
        ≡⟨ sym (pfac (cataBin nil' cons' y) y1 (cataBin nil' cons' y2) y3 
                                               (cataBin nil' cons' y4)) ⟩
      cons' (cons' (cataBin nil' cons' y) y1 (cataBin nil' cons' y2)) y3
                                             (cataBin nil' cons' y4) 
      ∎
    helper nil' cons' (bin (bin y y' y0) y1 y2) 
                      (bin y3 y4 y5) 
           pf (assoc pfac) (acc funx) (acc funy) = begin 
      cons' (cons' (cataBin nil' cons' y) y' (cataBin nil' cons' y0)) y1
            (cataBin nil' cons' y2)
        ≡⟨ pfac (cataBin nil' cons' y) y' 
                (cataBin nil' cons' y0) y1 
                (cataBin nil' cons' y2) ⟩
      cons' (cataBin nil' cons' y) y'
            (cons' (cataBin nil' cons' y0) y1 (cataBin nil' cons' y2)) 
        ≡⟨ helper nil' cons' (bin y y' (bin y0 y1 y2)) 
                             (bin y3 y4 y5) 
           (trans (sym (++-assoc (proj y) (cons y' (proj y0)) 
                                          (cons y1 (proj y2)))) pf) 
           (assoc pfac) (funx (bin y y' (bin y0 y1 y2)) binbin-lemma) (acc funy)
         ⟩
      cons' (cataBin nil' cons' y3) y4 (cataBin nil' cons' y5) 
      ∎



-- Do the whole thing again in 2 dimensions.


