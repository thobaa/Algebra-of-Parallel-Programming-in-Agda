module Cata where

open import Data.Product
open import Data.Nat
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open Relation.Binary.PropositionalEquality.≡-Reasoning


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
  tip : Bin a
  bin : Bin a -> a -> Bin a -> Bin a

cataBin : {a b : Set} -> (nil' : b) -> (bin' : b -> a -> b -> b) -> Bin a -> b
cataBin nil' bin' tip = nil'
cataBin nil' bin' (bin x x₁ x₂) = bin' (cataBin nil' bin' x) x₁ (cataBin nil' bin' x₂)


embed : ∀ {a} -> List a -> Bin a
embed nil = tip
embed (cons x xs) = bin tip x (embed xs)

proj : ∀ {a} -> Bin a -> List a
proj tip = nil
proj (bin xs x xs₁) = (proj xs) ++ (cons x (proj xs₁))

theorem : ∀ {a} -> (xs : List a) -> proj (embed xs) ≡ xs
theorem nil = refl
theorem (cons x xs) = cong (cons x) (theorem xs)


-- Associative bin' (bin' : b -> a -> b -> b) x a y b z
-- bin' associative om bin' (bin' x a y) b z == bin' x a (bin' y b z)
data associative {A B : Set} (f : B -> A -> B -> B) : Set where
  assoc : (∀ x a y b z -> f (f x a y) b z ≡ f x a (f y b z)) -> associative f
--  assoc 

-- proj nil = nil!!!


pf3 : {a : Set} {xs : List a} {ys : List a} -> ys ≢ nil -> xs ++ ys ≢ nil
pf3 {a} {xs} {nil} pf x = pf refl
pf3 {a} {nil} {cons y y'} pf x = pf x
pf3 {a} {cons y y'} {cons y0 y1} pf ()

cons≢nil : {a : Set} {x : a} {xs : List a} -> cons x xs ≢ nil
cons≢nil = λ ()

-- proj x == nil => x = refl
++cons≢nil : {a : Set} {xs : List a} {y : a} {ys : List a} -> (xs ++ cons y ys) ≢ nil
++cons≢nil {a} {xs} {y} {ys} x = pf3 {a} {xs} {cons y ys} (cons≢nil {a} {y} {ys}) x

pf : {a : Set} {x : Bin a} -> proj x ≡ nil -> x ≡ tip
pf {_} {tip} px≡nil = refl
pf {a} {bin y y' y0} px≡nil = ⊥-elim (++cons≢nil {a} {proj y} {_} {_} px≡nil) 

pf' : ∀ {X} {x : Bin X} -> x ≡ tip -> proj x ≡ nil
pf' {_} {tip} x≡tip = refl
pf' {_} {bin y y' y0} ()

cong₃ : {X Y Z W : Set} {x1 x2 : X} {y1 y2 : Y} {z1 z2 : Z}
  (f : X → Y → Z → W) → x1 ≡ x2 -> y1 ≡ y2 -> z1 ≡ z2 -> f x1 y1 z1 ≡ f x2 y2 z2
cong₃ {_} {_} {_} {_} {x1} {x2} {y1} {y2} {z1} {z2} f pfx pfy pfz = begin 
  f x1 y1 z1 ≡⟨ cong₂ (λ y z → f x1 y z) pfy pfz ⟩
  f x1 y2 z2 ≡⟨ cong (λ z → f z y2 z2) pfx ⟩
  f x2 y2 z2 ∎

conslemma : ∀ {a} {x y : a} {xs ys : List a} -> cons x xs ≡ cons y ys -> xs ≡ ys
conslemma refl = refl

conslemma2 : ∀ {A} {x y : A} {xs ys : List A} -> cons x xs ≡ cons y ys -> x ≡ y
conslemma2 refl = refl

++lemma : ∀ {A} {xs ys : List A} {x y : A} -> xs ++ (cons x nil) ≡ ys ++ (cons y nil) -> x ≡ y 
++lemma {A} {nil} {nil} refl = refl 
++lemma {A} {nil} {cons c cs} {x} {y} pf = ⊥-elim (++cons≢nil {A} {cs} {y} {nil} (sym (conslemma {A} {x} {c} pf)))
++lemma {A} {cons b bs} {nil} {x} {y} pf = ⊥-elim (++cons≢nil {A} {bs} {x} {nil} (conslemma {A} {b} {y} pf))
++lemma {A} {cons b bs} {cons c cs} {x} {y} pf = ++lemma {A} {bs} {cs} {x} {y} (conslemma pf)

++lemma2 : ∀ {A} {xs ys : List A} {x y : A} -> xs ++ (cons x nil) ≡ ys ++ (cons y nil) -> xs ≡ ys
++lemma2 {A} {nil} {nil} refl = refl 
++lemma2 {A} {nil} {cons c cs} {x} {y} pf = ⊥-elim (++cons≢nil {A} {cs} {y} {nil} (sym (conslemma {A} {x} {c} pf)))
++lemma2 {A} {cons b bs} {nil} {x} {y} pf = ⊥-elim (++cons≢nil {A} {bs} {x} {nil} (conslemma {A} {b} {y} pf))
++lemma2 {A} {cons b bs} {cons c cs} {x} {y} pf = cong₂ (λ x' xs → cons x' xs) (conslemma2 pf) (++lemma2 {A} {bs} {cs} {x} {y} (conslemma pf))

open import Data.Sum
open import Induction
open import Induction.WellFounded
open import Relation.Binary



-- small step I guess
data _<TP_ {a : Set} : Bin a × Bin a -> Bin a × Bin a -> Set where
  <TP-left  : ∀ {t1 t2 t : Bin a} {x : a} -> (t1 , t2) <TP (bin t1 x t , t2)
  <TP-right : ∀ {t1 t2 t : Bin a} {x : a} -> (t1 , t2) <TP (t1 , bin t2 x t)
--  (bin y y' (bin y0 y1 y2) , bin y3 y4 y5) <TP 
                   --  (bin (bin y y' y0) y1 y2 , bin y3 y4 y5)

data _<TP'_ {a : Set} : Bin a × Bin a -> Bin a × Bin a -> Set where
  <TP'-tipl : ∀ {t1 t2 t3 x} -> (tip , tip) <TP' (bin t1 x t2 , t3)
  <TP'-tipr : ∀ {t1 t2 t3 x} -> (tip , tip) <TP' (t1 , bin t2 x t3)
  <TP'-binl : ∀ {x y z å ä ö a b} -> (bin x y z , å) <TP' (bin (bin x ä ö) a b , å)
  <TP'-binr : ∀ {x y z å ä ö a b} -> (å , bin x y z) <TP' (å , bin (bin x ä ö) a b)

access : {a : Set} -> (t1t2 : Bin a × Bin a) -> (s1s2 : Bin a × Bin a) ->
           s1s2 <TP' t1t2 -> Acc _<TP'_ s1s2
access (tip , .(bin t2 x t3)) .(tip , tip) (<TP'-tipr {.tip} {t2} {t3} {x}) = acc (λ y ())
access (tip , .(bin (bin x ä ö) a' b)) .(tip , bin x y z) (<TP'-binr {x} {y} {z} {.tip} {ä} {ö} {a'} {b}) = acc (access (tip , bin x y z))
access (bin y y' y0 , proj₂) .(tip , tip) <TP'-tipl = acc (λ x ())
access (bin y y' y0 , .(bin t2 x t3)) .(tip , tip) (<TP'-tipr {.(bin y y' y0)} {t2} {t3} {x}) = acc (λ x' ())
access (bin .(bin x ä ö) y' y0 , proj₂) .(bin x y z , proj₂) (<TP'-binl {x} {y} {z} {.proj₂} {ä} {ö}) = acc (access (bin x y z , proj₂))
access (bin y y' y0 , .(bin (bin x ä ö) a' b)) .(bin y y' y0 , bin x y1 z) (<TP'-binr {x} {y1} {z} {.(bin y y' y0)} {ä} {ö} {a'} {b}) = acc (access (bin y y' y0 , bin x y1 z))

<TP'-wf : {a : Set} -> Well-founded (_<TP'_ {a})
<TP'-wf {a} t = acc (access t)

bccess : {a : Set} -> (t1t2 : Bin a × Bin a) -> (s1s2 : Bin a × Bin a) ->
           s1s2 <TP t1t2 -> Acc _<TP_ s1s2
bccess .(bin t1 x t' , t2) .(t1 , t2) (<TP-left {t1} {t2} {t'} {x}) = acc (bccess (t1 , t2))
bccess .(t1 , bin t2 x t') .(t1 , t2) (<TP-right {t1} {t2} {t'} {x}) = acc (bccess (t1 , t2))

<TP-wf : {a : Set} -> Well-founded (_<TP_ {a})
<TP-wf {a} t = acc (bccess t)


-- ideally would want arbitrary param
--postulate a : Set
--open All (<TP-wf {a})

{-
RecStruct : ∀ {a} → Set a → Set (suc a)
RecStruct {a} A = Pred A a → Pred A a


Recursor : ∀ {a} {A : Set a} → RecStruct A → Set _
Recursor Rec = ∀ P → Rec P ⊆′ P → Universal P


wfRec : Recursor (WfRec _<_)
wfRec = build wfRec-builder
-}
{-
test : {a b : Set} {nil' : b} {cons' : b → a → b → b} (x y : Bin a) →
         proj x ≡ proj y →
         associative cons' → cataBin nil' cons' x ≡ cataBin nil' cons' y
test = wfRec {!!} {!!} {!!}
  where
  helper : (n : _) → {!!}
  helper = {!!}-}


{-lemma2 : (proj yll ++ cons y1 (proj ylr)) ++ cons y (proj yr) ≡
             proj yll ++ cons y1 (proj ylr ++ cons y (proj yr))
lemma2 = ++-assoc (proj yll) (cons y1 (proj ylr)) (cons y (proj yr))
lemma1 :  cataBin nil' cons' (bin yll y1 (bin ylr y yr)) ≡ 
            cataBin nil' cons' (bin (bin yll y1 ylr) y yr)         
lemma1 = begin 
    cataBin nil' cons' (bin yll y1 (bin ylr y yr)) 
            ≡⟨ sym (pfac (cataBin nil' cons' yll) y1 (cataBin nil' cons' ylr) y
                      (cataBin nil' cons' yr)) ⟩ 
    cataBin nil' cons' (bin (bin yll y1 ylr) y yr) ∎
-}

exercise' : {a b : Set} {nil' : b} {cons' : b -> a -> b -> b} (x y : Bin a) -> 
  proj x ≡ proj y -> associative cons' -> 
  cataBin nil' cons' x ≡  cataBin nil' cons' y -- Assoc cons' !!!
-- tip tip
exercise' {a} {b} {nil'} {cons'} t s pxpy ac =  helper nil' cons' (t , s ) pxpy ac (acc (access (t , s)))
  where
    helper : {a b : Set} (nil' : b) (cons' : b -> a -> b -> b) 
      (xy : Bin a × Bin a) -> 
      proj (proj₁ xy) ≡ proj (proj₂ xy) -> associative cons' -> Acc _<TP'_ xy -> 
      cataBin nil' cons' (proj₁ xy) ≡  cataBin nil' cons' (proj₂ xy)
    helper _ _ (tip , tip) pf ac' _ = refl
    helper _ _ (tip , bin y y' y0) pf ac' _ = ⊥-elim (++cons≢nil {_} {proj y} (sym pf))
    helper _ _ (bin y y' y0 , tip) pf ac' _ = ⊥-elim (++cons≢nil {_} {proj y} pf)
    helper nil' cons' (bin tip y' y0 , bin tip y2 y3) pf ac' (acc fun) = cong₂ (λ x x' → cons' nil' x x') (conslemma2 pf) (helper nil' cons' (y0 , y3) (conslemma pf) ac' (fun {!!} {!!}))
    helper nil' cons' (bin tip y' y0 , bin (bin y y1 y2) y3 y4) pf (assoc pfac)  (acc fun) = begin 
      cons' nil' y' (cataBin nil' cons' y0) 
        ≡⟨ helper nil' cons' (bin tip y' y0 , bin y y1 (bin y2 y3 y4)) (trans pf (++-assoc (proj y) (cons y1 (proj y2)) (cons y3 (proj y4)))) (assoc pfac) (fun (bin tip y' y0 , bin y y1 (bin y2 y3 y4)) <TP'-binr) ⟩ 
      cons' (cataBin nil' cons' y) y1
        (cons' (cataBin nil' cons' y2) y3 (cataBin nil' cons' y4)) 
        ≡⟨ sym (pfac (cataBin nil' cons' y) y1 (cataBin nil' cons' y2) y3 (cataBin nil' cons' y4)) ⟩
      cons' (cons' (cataBin nil' cons' y) y1 (cataBin nil' cons' y2)) y3
        (cataBin nil' cons' y4) ∎ -- helper {a} {nil'} {cons'} (bin tip y' y0 , bin y y1 (bin y2 y3 y4)) pf ac'
    helper nil' cons' (bin (bin y y' y0) y1 y2 , bin y3 y4 y5) pf (assoc pfac) (acc fun) = begin 
      cons' (cons' (cataBin nil' cons' y) y' (cataBin nil' cons' y0)) y1
        (cataBin nil' cons' y2)
        ≡⟨ pfac (cataBin nil' cons' y) y' (cataBin nil' cons' y0) y1 (cataBin nil' cons' y2) ⟩
      cons' (cataBin nil' cons' y) y'
        (cons' (cataBin nil' cons' y0) y1 (cataBin nil' cons' y2)) 
        ≡⟨ helper nil' cons' (bin y y' (bin y0 y1 y2) , bin y3 y4 y5) (trans (sym (++-assoc (proj y) (cons y' (proj y0)) (cons y1 (proj y2)))) pf) (assoc pfac)             (fun (bin y y' (bin y0 y1 y2) , bin y3 y4 y5) <TP'-binl)  ⟩
      cons' (cataBin nil' cons' y3) y4 (cataBin nil' cons' y5) ∎

{-
exercise : {a b : Set} {nil' : b} {cons' : b -> a -> b -> b} (x y : Bin a) -> 
  proj x ≡ proj y -> associative cons' -> 
  cataBin nil' cons' x ≡  cataBin nil' cons' y -- Assoc cons' !!!
-- tip tip
exercise tip tip pxpy ac = refl
-- tip bin
exercise tip (bin y y' y0) pxpy ac = ⊥-elim (++cons≢nil {_} {proj y} (sym pxpy))
-- bin tip
exercise (bin y y' y0) tip pxpy ac = ⊥-elim (++cons≢nil {_} {proj y} pxpy)
--exercise {A} {b} {nil'} {cons'} (bin xl x tip) (bin yl y tip) pxpy (assoc pfac) = cong₃ cons' (exercise xl yl (++lemma2 pxpy) (assoc pfac)) (++lemma {A} {proj xl} {proj yl} {x} {y} pxpy) refl

-- (bin tip) (bin tip)
exercise {A} {b} {nil'} {cons'} (bin tip x xr) (bin tip y yr) pxpy pfac = cong₂ (λ x' y' → cons' nil' x' y') (conslemma2 pxpy) (exercise xr yr (conslemma pxpy) pfac)

-- (bin tip) (bin bin)
exercise {A} {b} {nil'} {cons'} (bin tip x xr) (bin (bin yll y1 ylr) y yr) pxpy (assoc pfac) = begin 
  cataBin nil' cons' (bin tip x xr)
          ≡⟨ exercise {A} {b} {nil'} {cons'} 
             (bin tip x xr) 
             (bin yll y1 (bin ylr y yr)) 
             (trans pxpy lemma2) (assoc pfac) ⟩ 
  cataBin nil' cons' (bin yll y1 (bin ylr y yr)) 
          ≡⟨ lemma1 ⟩
  cataBin nil' cons' (bin (bin yll y1 ylr) y yr) ∎
  where 
  lemma2 : (proj yll ++ cons y1 (proj ylr)) ++ cons y (proj yr) ≡
             proj yll ++ cons y1 (proj ylr ++ cons y (proj yr))
  lemma2 = ++-assoc (proj yll) (cons y1 (proj ylr)) (cons y (proj yr))
  lemma1 :  cataBin nil' cons' (bin yll y1 (bin ylr y yr)) ≡ 
            cataBin nil' cons' (bin (bin yll y1 ylr) y yr)         
  lemma1 = begin 
    cataBin nil' cons' (bin yll y1 (bin ylr y yr)) 
            ≡⟨ sym (pfac (cataBin nil' cons' yll) y1 (cataBin nil' cons' ylr) y
                      (cataBin nil' cons' yr)) ⟩ 
    cataBin nil' cons' (bin (bin yll y1 ylr) y yr) ∎
{-Goal: cons' nil' y (cataBin nil' cons' yr) ≡
    cons' (cataBin nil' cons' xll) x1
    (cons' (cataBin nil' cons' xlr) x2 (cataBin nil' cons' xr))
-}

-- om man bara använder det på delträdet???

-- (bin bin) (bin tip)
exercise {A} {b} {nil'} {cons'} (bin (bin xll x1 xlr) x2 xr) (bin yl y yr) pxpy (assoc pfac) = sym (begin 
  cataBin nil' cons' (bin yl y yr) ≡⟨ {!!} ⟩
  cataBin nil' cons' (bin xll x1 (bin xlr x2 xr)) ≡⟨ {!!} ⟩ 
  cataBin nil' cons' (bin (bin xll x1 xlr) x2 xr) ∎)


-}





-- Do the whole thing again in 2 dimensions.


