
{-
  cataBin nil' cons' (bin (bin xll x1 xlr) x2 xr) ≡⟨ pfac (cataBin nil' cons' xll) x1 (cataBin nil' cons' xlr) x2 (cataBin nil' cons' xr) ⟩
  cataBin nil' cons' (bin xll x1 (bin xlr x2 xr)) 
    ≡⟨ cong (λ x → cons' x x1 (cons' (cataBin nil' cons' xlr) x2 (cataBin nil' cons' xr))) (exercise {A} {b} {nil'} {cons'} xll {!!} {!!} (assoc pfac)) ⟩
  {!!} ≡⟨ {!!} ⟩
  
  cataBin nil' cons' (bin tip y yr) ∎-}
--Goal: cons' (cataBin nil' cons' xll) x1
--      (cons' (cataBin nil' cons' xlr) x2 (cataBin nil' cons' xr))
--      ≡ cons' nil' y (cataBin nil' cons' yr)
--exercise {A} {b} {nil'} {cons'} (bin xll x1 (bin xlr x2 xr)) (bin tip y yr)  (trans (sym (++-assoc (proj xll) (cons x1 (proj xlr)) (cons x2 (proj xr)))) pxpy) (assoc pfac) 

--exercise {A} {b} {nil'} {cons'} (bin (bin xll x1 xlr) x2 xr) (bin (bin yll y1 ylr) y2 yr) pxpy (assoc pfac) = {!!}
{-exercise {A} {b} {nil'} {cons'} (bin (bin xll x1 xlr) x2 xr) (bin tip y yr) pxpy (assoc pfac) with proj xll | inspect proj xll 
... | nil | [ pfnil ] = begin 
  cons' (cons' (cataBin nil' cons' xll) x1 (cataBin nil' cons' xlr)) x2 
    (cataBin nil' cons' xr) 
    ≡⟨ pfac (cataBin nil' cons' xll) x1 (cataBin nil' cons' xlr) x2 (cataBin nil' cons' xr) ⟩
  cons' (cataBin nil' cons' xll) x1
    (cons' (cataBin nil' cons' xlr) x2 (cataBin nil' cons' xr)) 
    ≡⟨ cong₃ (λ x y' z → cons' x y' z) (exercise xll tip pfnil (assoc pfac)) (conslemma2 pxpy) (exercise (bin xlr x2 xr) yr (conslemma pxpy) (assoc pfac)) ⟩ -- cons' (cataBin nil' cons' xlr) x2 (cataBin nil' cons' xr) ≡      cataBin nil' cons' yr
  cons' nil' y (cataBin nil' cons' yr) ∎
... | cons a as | [ pfcons ] = begin 
  cons' (cons' (cataBin nil' cons' xll) x1 (cataBin nil' cons' xlr))
    x2 (cataBin nil' cons' xr) 
    ≡⟨ pfac (cataBin nil' cons' xll) x1 (cataBin nil' cons' xlr) x2 (cataBin nil' cons' xr) ⟩

  cons' (cataBin nil' cons' xll) x1 (cons' (cataBin nil' cons' xlr) x2 (cataBin nil' cons' xr))
    ≡⟨ {!!} ⟩ -- exercise {A} {b} {nil'} {cons'} (bin xll x1 (bin xlr x2 xr)) (bin tip y yr) {!!} (assoc pfac) ⟩
  cons' nil' y (cataBin nil' cons' yr) ∎-}


{-exercise {A} {b} {nil'} {cons'} (bin (bin tip x1 xlr) x2 xr) (bin tip y yr) pxpy (assoc pfac) with inspect (proj xll = begin 
  cataBin nil' cons' (bin (bin tip x1 xlr) x2 xr)
  ≡⟨ refl ⟩
  cons' (cons' (cataBin nil' cons' tip) x1 (cataBin nil' cons' xlr)) x2
        (cataBin nil' cons' xr)
  ≡⟨ pfac (cataBin nil' cons' tip) x1 (cataBin nil' cons' xlr) x2
       (cataBin nil' cons' xr) ⟩
  cons' (cataBin nil' cons' tip) x1 (cons' (cataBin nil' cons' xlr) x2
        (cataBin nil' cons' xr))
  ≡⟨ {!!} ⟩
  cataBin nil' cons' (bin tip y yr) ∎
  
exercise {A} {b} {nil'} {cons'} (bin (bin (bin xlll x0 xllr) x1 xlr) x2 xr) (bin tip y yr) pxpy (assoc pfac) = {!!}
-}
{-exercise {A} {b} {nil'} {cons'} (bin (bin xll x1 xlr) x2 xr) (bin tip y yr) pxpy (assoc pfac) = sym (begin 
  cataBin nil' cons' (bin tip y yr)
    ≡⟨ sym (exercise {A} {b} {nil'} {cons'} (bin xll x1 (bin xlr x2 xr)) (bin tip y yr) (trans (sym (++-assoc (proj xll) (cons x1 (proj xlr)) (cons x2 (proj xr)))) pxpy) (assoc pfac)) ⟩
  cataBin nil' cons' (bin xll x1 (bin xlr x2 xr)) ≡⟨ {!!} ⟩ 
  cataBin nil' cons' (bin (bin xll x1 xlr) x2 xr) ∎)
  -}

{-sym (begin 
  cataBin nil' cons' (bin (bin xll x1 xlr) x2 xr) ≡⟨ lemma1 ⟩ 
  cataBin nil' cons' (bin xll x1 (bin xlr x2 xr)) ≡⟨ {!!} ⟩
  {-exercise {A} {b} {nil'} {cons'} (bin xll x1 (bin xlr x2 xr)) (bin tip y yr) lemma2 (assoc pfac) ⟩-}
  cataBin nil' cons' (bin tip y yr) ∎)
  where
  lemma1 :  cataBin nil' cons' (bin (bin xll x1 xlr) x2 xr)  ≡ 
            cataBin nil' cons' (bin xll x1 (bin xlr x2 xr)) 
  lemma1 = begin 
    cataBin nil' cons' (bin (bin xll x1 xlr) x2 xr)
      ≡⟨ pfac (cataBin nil' cons' xll) x1 (cataBin nil' cons' xlr) x2 (cataBin nil' cons' xr) ⟩

--Goal: cons'
--      (cons' (cataBin nil' cons' xll) x1 (cataBin nil' cons' xlr)) x2
--      (cataBin nil' cons' xr)
--      ≡
--      cons' (cataBin nil' cons' xll) x1
--      (cons' (cataBin nil' cons' xlr) x2 (cataBin nil' cons' xr))
    cataBin nil' cons' (bin xll x1 (bin xlr x2 xr))  ∎-}







{-with proj xll
... | nil = begin 
  cons' (cons' (cataBin nil' cons' xll) x1 (cataBin nil' cons' xlr))
    x2 (cataBin nil' cons' xr) 
    ≡⟨ pfac (cataBin nil' cons' xll) x1 (cataBin nil' cons' xlr) x2
         (cataBin nil' cons' xr) ⟩ 
  cons' (cataBin nil' cons' xll) x1 (cons' (cataBin nil' cons' xlr)
    x2 (cataBin nil' cons' xr))
  ≡⟨ refl ⟩
  cons' (cataBin nil' cons' xll) x1 (cataBin nil' cons' (bin xlr x2 xr))
    ≡⟨ cong₃ (λ x y' z → cons' x y' z) ({!!} --exercise xll tip {!refl!} (assoc pfac)
  ) x1≡y (exercise (bin xlr x2 xr) yr rest≡rest (assoc pfac)) ⟩ 
  -- Goal: cataBin nil' cons' xll ≡ nil'
  cons' nil' y (cataBin nil' cons' yr) ∎
  where 
  x1≡y : x1 ≡ y 
  x1≡y = conslemma2 pxpy
  rest≡rest : proj xlr ++ cons x2 (proj xr) ≡ proj yr
  rest≡rest = conslemma pxpy
... | cons a as  = begin 
  cons' (cons' (cataBin nil' cons' xll) x1 (cataBin nil' cons' xlr))
    x2 (cataBin nil' cons' xr) 
    ≡⟨ pfac (cataBin nil' cons' xll) x1 (cataBin nil' cons' xlr) x2
         (cataBin nil' cons' xr) ⟩ 
  cons' (cataBin nil' cons' xll) x1 (cons' (cataBin nil' cons' xlr)
    x2 (cataBin nil' cons' xr))
  ≡⟨ refl ⟩
  cons' (cataBin nil' cons' xll) x1 (cataBin nil' cons' (bin xlr x2 xr))
    ≡⟨ cong₃ (λ x y' z → cons' x y' z) {!!} {!a≡y!} {!!} ⟩ 
  cons' nil' y (cataBin nil' cons' yr) ∎
  where 
  a≡y : a ≡ y 
  a≡y = conslemma2 pxpy
  rest≡rest : (as ++ cons x1 (proj xlr)) ++ cons x2 (proj xr) ≡ proj yr
  rest≡rest = conslemma pxpy
exercise {A} {b} {nil'} {cons'} (bin tip x xr) (bin (bin yll y1 ylr)  y2 yr) pxpy (assoc pfac) = {!!}
exercise {A} {b} {nil'} {cons'} (bin (bin xll x1 xlr) x2 xr) (bin (bin yll y1 ylr) y2 yr) pxpy (assoc pfac) = {!!}

-}
{-
exercise {a} {b} {nil'} {cons'} (bin xl x tip) (bin yl y (bin yrl y2 yrr) ) pxpy (assoc pfac) = sym (begin 
  cons' (cataBin nil' cons' yl) y (cons' (cataBin nil' cons' yrl) y2 (cataBin nil' cons' yrr)) 
                 ≡⟨ sym (pfac (cataBin nil' cons' yl) y (cataBin nil' cons' yrl) y2 (cataBin nil' cons' yrr)) ⟩
  cons' (cons' (cataBin nil' cons' yl) y (cataBin nil' cons' yrl)) y2
    (cataBin nil' cons' yrr)           
                 ≡⟨ {!cong!} ⟩ -- försöker göra höger delträd mindre!
  cons' (cataBin nil' cons' xl) x nil' ∎)
-}

{-exercise {a} {b} {nil'} {cons'} (bin xl x (bin xrl x2 xrr)) (bin yl y yr) pxpy (assoc pfac) =
  begin 
  cons' (cataBin nil' cons' xl) x (cataBin nil' cons' (bin xrl x2 xrr)) ≡⟨ sym (pfac (cataBin nil' cons' xl) x (cataBin nil' cons' xrl) x2 (cataBin nil' cons' xrr)) ⟩
  cons' (cons' (cataBin nil' cons' xl) x (cataBin nil' cons' xrl)) x2 (cataBin nil' cons' xrr) ≡⟨ {!!} ⟩
  cons' (cataBin nil' cons' yl) y (cataBin nil' cons' yr) ∎
-}
{-
Goal: _298 xl x xrl x2 xrr yl y yr pxpy pfac ≡
      cons' (cataBin nil' cons' xl) x
      (cons' (cataBin nil' cons' xrl) x2 (cataBin nil' cons' xrr))
Have: (x' : b) (a' : a) (y' : b) (b' : a) (z : b) →
      cons' (cons' x' a' y') b' z ≡ cons' x' a' (cons' y' b' z)
-}
--Goal: cons' (cataBin nil' cons' xl) x
--      (cons' (cataBin nil' cons' xrl) x2 (cataBin nil' cons' xrr))
--      ≡ _298 xl x xrl x2 xrr yl y yr pxpy pfac
--exercise nil y px≡py as with proj nil
--exercise nil y px≡py as | nail = {!!}
{-exercise {a} {b} tip tip px≡py as  = refl
exercise {a} {b} x y px≡py as  with proj x | proj y | pf'{_} {x}
exercise tip tip _ as | px | py = refl
exercise tip (bin y y' y0) px≡py as | px | nil = {!!}
exercise tip (bin y y' y0) px≡py as | px | cons y1 y2 = ⊥-elim {!pf' {_} {px} refl!}
exercise (bin q w e) tip px≡py as | px | py = {!!}
exercise (bin q w e) (bin y y' y0) px≡py as | px | pb = {!!}
-}

{-
exercise {a} {b} {nil'} {cons'} x y px≡py _  with proj x | proj y
exercise x y refl y' | nil | nil = {!!}
exercise x y ()    _ | nil | cons _ _
exercise x y ()    _ | cons _ _ | nil
exercise x y px≡py as | cons y' y0 | cons y1 y2 = {!!}
-}

{-exercise nil y px≡py _ with y | proj y
--exercise nil y px≡py a with proj y
... | nil | nil = refl -- = {!!}
exercise nil y refl y' | bin a' b c | nil = {!!}
... | aaa | cons y' y's = {!!}
exercise (bin y y' y0) nil px≡py (assoc x' a' y2 b' z y3) = {!px≡py!}
exercise (bin y y' y0) (bin y1 y2 y3) px≡py (assoc x' a' y4 b' z y5) = {!!}
-}
-- vill man inte visa att proj (cataBin nil' bin' (embed xs)) == cataList 




{-<TP-wf : {a : Set} -> Well-founded (_<TP_ {a})
<TP-wf {a} t = acc (access t)
  where
  access : {a : Set} -> (t1t2 : Bin a × Bin a) -> (s1s2 : Bin a × Bin a) -> 
                        s1s2 <TP t1t2 -> Acc _<TP_ s1s2
  access (tip , tip) s (proj₁ , inj₁ ())
  access (tip , tip) s (proj₁ , inj₂ ())
  access (tip , bin y y' y0) (tip , tip) (proj₁ , inj₁ x) = access {!!} (tip , tip) {!proj₁!}
  access (tip , bin y y' y0) (tip , tip) (proj₁ , inj₂ y1) = {!!}
  access (tip , bin y y' y0) (tip , bin y1 y2 y3) pf = {!!}
  access (tip , bin y y' y0) (bin y1 y2 y3 , proj₂) pf = {!!}
  access (bin y y' y0 , proj₂) s pf = {!!}-}

{-  access : {a : Set} -> (t1t2 : Bin a × Bin a) -> (s1s2 : Bin a × Bin a) ->
           s1s2 <TP t1t2 -> Acc _<TP_ s1s2
  access (tip , tip) s ()
  access (tip , bin tip y' y0) .(tip , tip) <TP-right = acc (λ y ())
  access (tip , bin (bin y y' y0) y1 y2) .(tip , bin y y' y0) <TP-right = 
    acc (access (tip , bin y y' y0))
--acc (λ y3 <TP-right → {!y3!})
-- Goal: Acc _<TP_ (tip , bin y y' y0)
  access (bin tip y' y0 , tip) .(tip , tip) <TP-left = acc (λ y ())
  access (bin (bin y y' y0) y1 y2 , tip) .(bin y y' y0 , tip) <TP-left = acc (access (bin y y' y0 , tip))
  access (bin y y' y0 , bin y1 y2 y3) (tip , tip) ()
  access (bin .tip y' y0 , bin y1 y2 y3) (tip , bin .y1 .y2 .y3) <TP-left = acc (access (tip , bin y1 y2 y3))
--Goal: Acc _<TP_ (tip , bin y1 y2 y3)
  access (bin .(bin y4 y5 y6) y' y0 , bin y1 y2 y3) (bin y4 y5 y6 , .(bin y1 y2 y3)) <TP-left = acc (access (bin y4 y5 y6 , bin y1 y2 y3))
--Goal: Acc _<TP_ (bin y4 y5 y6 , bin y1 y2 y3)
  access (bin y y' y0 , bin y1 y2 y3) (bin .y .y' .y0 , .y1) <TP-right = acc (access (bin y y' y0 , y1))-}

{-
data _≤TP_ {a : Set} : Bin a × Bin a -> Bin a × Bin a -> Set where
  ≤TP-refl  : ∀ {t1 t2 : Bin a} -> (t1 , t2) ≤TP (t1 , t2)
  ≤TP-left  : ∀ {t1 t2 t3 t4 t : Bin a} {x : a}  -> 
              (t1 , t2) ≤TP (t3 , t4) -> (t1 , t2) ≤TP (bin t3 x t , t4)
  ≤TP-right : ∀ {t1 t2 t3 t4 t : Bin a} {x : a} -> 
              (t1 , t2) ≤TP (t3 , t4) -> (t1 , t2) ≤TP (t3 , bin t4 x t)

_<TP_ : {a : Set} -> Bin a × Bin a -> Bin a × Bin a -> Set
_<TP_ {a} (t1 , t2) (t3 , t4) = ∃ (λ (xt : a × Bin a) →
        ((bin t1 (proj₁ xt) (proj₂ xt) , t2) ≤TP (t3 , t4)) ⊎ 
        ((t1 , bin t2 (proj₁ xt) (proj₂ xt)) ≤TP (t3 , t4)))

-}

--_<H_ :  {a : Set} -> Bin a -> Bin a -> Set     
--_<H_ = {!!}

--_<T_ : {a : Set} -> Bin a -> Bin a -> Set     
--m <T n = ∃ (λ x -> bin m x {!t!} ≤T n)

{-<H-wf : {a : Set} -> Well-founded (_<H_ {a})
<H-wf {a} t = acc (access t)
  where
    access : (t' : Bin a) → (s : Bin a) → s <H t' → Acc _<H_ s
    access tip s (<H-left ())
    access tip s (<H-right ())
    access (bin y y' y0) s pf = {!s!}
-}

 --++lemma2 {A} {{!bs!}} {{!!}} {{!!}} {{!!}} ({!!})
{-
import Data.Nat

-}

{-


data LeftDepth : Set where 
  ld : 

leftdepth : ∀ {A} -> Bin A -> ℕ
leftdepth tip = 0
leftdepth (bin y y' y0) = 1 + leftdepth y 

sumDepth : LeftDepth -> LeftDepth -> LeftDepth
sumDepth = {!!}

helper : {a b : Set} {nil' : b} {cons' : b -> a -> b -> b} (x y : Bin a) -> 
  proj x ≡ proj y -> associative cons' -> LeftDepth -> 
  cataBin nil' cons' x ≡ cataBin nil' cons' y
helper = {!!}
-}

TreePair : {a : Set} -> Bin a -> Bin a -> Bin a × Bin a
TreePair = _,_

--open import Level
--data Smaller (A : Set) : Rel (Bin A) Level.zero where
--  aa : Bin A -> Bin A -> Smaller A
--data Acc {a : Set}(_<_ : a -> a -> Set) : a -> Set where
--data ∃ (a : Set) (b : a -> Set) : Set where 
leftDepth : {a : Set} -> Bin a -> ℕ
leftDepth tip = 0
leftDepth (bin y y' y0) = suc (leftDepth y)

rightDepth : {a : Set} -> Bin a -> ℕ
rightDepth tip = 0
rightDepth (bin y y' y0) = suc (rightDepth y0)

data _<H_ {a : Set} : Bin a -> Bin a -> Set where
  <H-left  : ∀ {t1 t2} -> leftDepth  t1 < leftDepth  t2 -> t1 <H t2
  <H-right : ∀ {t1 t2} -> rightDepth t1 < rightDepth t2 -> t1 <H t2
  
data _<T_ {a : Set} : Bin a -> Bin a -> Set where
  --≤T-refl  : ∀ {t} -> t ≤T t
  <T-left  : ∀ {t1 t2 t3 x} -> t1 <T t2 -> t1 <T bin t2 x t3
--  ≤T-right : ∀ {t1 t2 t3 x} -> t1 ≤T t2 -> t1 ≤T bin t3 x t2

<T-wf : {a : Set} -> Well-founded (_<T_ {a})
<T-wf {a} t = acc (access t)
  where 
  access : {a : Set} (t' : Bin a) → (s : Bin a) → s <T t' → Acc _<T_ s
  access tip s ()
  access (bin y y' y0) s (<T-left y1) = access y s y1

    


{-cccess : {a : Set} -> (t : Bin a) -> (s : Bin a) ->
           s <T t -> Acc _<T_ s
cccess tip s (<T-intr ())
cccess (bin y y' y0) tip (<T-intr y1) = acc (λ y2 x → ⊥-elim (x≮Ttip x))
cccess (bin y y' y0) (bin y1 y2 y3) pf = acc (λ y4 x → {!!})
-}
-- small step I guess
data _<TP_ {a : Set} : Bin a × Bin a -> Bin a × Bin a -> Set where
  <TP-left  : ∀ {t1 t2 t : Bin a} {x : a} -> (t1 , t2) <TP (bin t1 x t , t2)
  <TP-right : ∀ {t1 t2 t : Bin a} {x : a} -> (t1 , t2) <TP (t1 , bin t2 x t)
--  (bin y y' (bin y0 y1 y2) , bin y3 y4 y5) <TP 
                   --  (bin (bin y y' y0) y1 y2 , bin y3 y4 y5)

data _<TP'_ {a : Set} : Bin a × Bin a -> Bin a × Bin a -> Set where
  <TP'-tipl : ∀ {t1 t2 t3 x} -> (tip , tip) <TP' (bin t1 x t2 , t3)
  <TP'-tipr : ∀ {t1 t2 t3 x} -> (tip , tip) <TP' (t1 , bin t2 x t3)
--  <TP'-bitl : ∀ {x y z å} -> (y , å )    <TP' (bin tip x y , bin tip z å)
  <TP'-binl : ∀ {x y z å ä ö a b} -> (bin x y z , å) <TP' (bin (bin x ä ö) a b , å)
  <TP'-binr : ∀ {x y z å ä ö a b} -> (å , bin x y z) <TP' (å , bin (bin x ä ö) a b)

access : {a : Set} -> (t1t2 : Bin a × Bin a) -> (s1s2 : Bin a × Bin a) ->
           s1s2 <TP' t1t2 -> Acc _<TP'_ s1s2
{-
access (tip , .(bin t2 x t3)) .(tip , tip) (<TP'-tipr {.tip} {t2} {t3} {x}) = acc (λ x' ())
access (tip , .(bin (bin x ä ö) a' b)) .(tip , bin x y z) (<TP'-binr {x} {y} {z} {.tip} {ä} {ö} {a'} {b}) = acc (access (tip , bin x y z))
access (bin y y' y0 , proj₂) .(tip , tip) <TP'-tipl = acc (λ x ())
access (bin y y' y0 , .(bin t2 x t3)) .(tip , tip) (<TP'-tipr {.(bin y y' y0)} {t2} {t3} {x}) = acc (λ x' ())
access (bin .tip y' y0 , .(bin tip z å)) .(y0 , å) (<TP'-bitl {.y'} {.y0} {z} {å}) = acc (access (y0 , å))
access (bin .(bin x ä ö) y' y0 , tip) .(bin x y z , tip) (<TP'-binl {x} {y} {z} {.tip} {ä} {ö}) = acc {!!}
access (bin .(bin x ä ö) y' y0 , bin y y1 y2) .(bin x y3 z , bin y y1 y2) (<TP'-binl {x} {y3} {z} {.(bin y y1 y2)} {ä} {ö}) = {!!}
access (bin y y' y0 , .(bin (bin x ä ö) a' b)) .(bin y y' y0 , bin x y1 z) (<TP'-binr {x} {y1} {z} {.(bin y y' y0)} {ä} {ö} {a'} {b}) = acc (access (bin y y' y0 , bin x y1 z))-}

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
