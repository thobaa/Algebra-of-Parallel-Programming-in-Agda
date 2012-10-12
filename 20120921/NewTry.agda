module NewTry where

open import Data.Nat
open import Data.Fin using (Fin; fromℕ; fromℕ≤; toℕ;  raise; reduce≥) 
                     renaming (zero to f0; suc to fsuc)

open import Data.Integer using (ℤ; +_; _-_)
                        -- renaming (≥ to z≥)
open import Definitions using (toℤ) renaming (_≥_ to _z≥_; _<_ to _z<_)
open import Data.Empty
open import ZLemmas
open import NatLemmas
open import Algebra
open import Algebra.Structures
open import Data.Product
open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Function
open import Relation.Nullary.Core



open import Level using () renaming (zero to Lzero)
Ring' : Set₁
Ring' = Ring Lzero Lzero

RC : Ring' -> Set
RC = Ring.Carrier

R+ : (a : Ring') -> RC a -> RC a -> RC a
R+ = Ring._+_

R* : (a : Ring') -> RC a -> RC a -> RC a
R* = Ring._*_


R0 : (a : Ring') -> Ring.Carrier a
R0 = Ring.0#

R1 : (a : Ring') -> Ring.Carrier a
R1 = Ring.1#

--toℤ : ∀ {n} -> Fin n -> ℤ
--toℤ f = + (toℕ f)

data Bin : Set where
  empty : Bin
  two   : Bin  -> Bin -> Bin

AbVec : (a : Ring') -> ℕ -> Set
AbVec a n = Fin n -> RC a

AbDot : ∀ {a n} -> AbVec a n -> AbVec a n -> RC a
AbDot {a} {zero} u v = R0 a
AbDot {a} {suc n} u v = R+ a (R* a (u f0) (v f0)) (AbDot {a}
                                          (λ i → u (fsuc i)) (λ j → v (fsuc j)))

-- Abstract matrix
AbMatrix : (a : Ring') -> ℕ -> ℕ -> Set
AbMatrix a m n = Fin m -> Fin n -> RC a

IsTrianguar : (a : Ring') -> ∀ {m n} -> (d : ℕ) -> (A : AbMatrix a m n) -> Set
IsTrianguar a {m} {n} d A = (i : Fin m) → (j : Fin n) → 
                     (toℤ j - toℤ i z< + d) → A i j ≡ R0 a

--AbUTMatrix : (a : Ring') -> (m : ℕ) -> (n : ℕ) -> (d : ℕ) -> Set
--             (A : AbMatrix a m n) -> IsTrianguar a m n d A -> Set
--AbUTMatrix a m n d A = {!!}

-- identity matrix!
AbId : ∀ a n -> AbMatrix a n n
AbId a zero () ()
AbId a (suc n) f0 f0 = R1 a
AbId a (suc n) f0 (fsuc i) = R0 a
AbId a (suc n) (fsuc i) f0 = R0 a
AbId a (suc n) (fsuc i) (fsuc i') = AbId a n i i'

-- Matrix addition
AbMatrix+ : ∀ a {m n} -> AbMatrix a m n -> AbMatrix a m n -> AbMatrix a m n
AbMatrix+ a A B = λ i j → R+ a (A i j) (B i j)

-- Matrix multiplication
AbMatrix* : ∀ a {n m p} -> AbMatrix a m n -> AbMatrix a n p -> AbMatrix a m p
AbMatrix* a A B = λ i j → AbDot {a} (A i) (λ k → B k j)

-- fromℕ≤ : ∀ {m n} → m N< n → Fin n
reduce≤ : ∀ {n m} -> (i : Fin (n + m)) -> (suc (toℕ i) ≤ n) -> Fin n
reduce≤ i pf = fromℕ≤ pf --fromℕ≤ {toℕ i} (s≤s pf)
--reduce≥ : ∀ {m n} (i : Fin (m N+ n)) (i≥m : toℕ i N≥ m) → Fin n
--j ∈ m + o, suc j > n -> j ≥ n


≰to> : ∀ {m n} -> m ≰ n -> m > n
≰to> {zero} {m} pf = ⊥-elim (pf z≤n)
≰to> {suc n} {zero} pf = s≤s z≤n
≰to> {suc n} {suc n'} pf = s≤s (≰to> (λ z → pf (s≤s z)))

-- Concatenation 
Ab++ : ∀ a {m n o} -> AbMatrix a m n -> AbMatrix a m o -> AbMatrix a m (n + o)
Ab++ a {m} {n} {o} A B i j with suc (toℕ j) ≤? n
...| yes p = A i (reduce≤ j p)
...| no ¬p = B i (reduce≥ j (p≤p (≰to> ¬p)))

-- Concatenation in other dimension
AbOver : ∀ a {m n o} -> AbMatrix a m n -> 
                        AbMatrix a o n -> AbMatrix a (m + o) n
AbOver a {m} {n} {o} A B i j with suc (toℕ i) ≤? m
...| yes p = A (reduce≤ i p) j
...| no ¬p = B (reduce≥ i (p≤p (≰to> ¬p))) j


-- Matrices
data Rec (a : Ring') : Bin -> Bin -> Set where
  one  : (x : RC a) -> Rec a empty empty
  side : ∀ {rt ct1 ct2} -> Rec a rt ct1 -> 
                           Rec a rt ct2 -> Rec a rt (two ct1 ct2)
  over : ∀ {rt1 rt2 ct} -> Rec a rt1 ct -> Rec a rt2 ct -> 
                                           Rec a (two rt1 rt2) ct


data Splitting : Set where
  empty : Splitting -- no extent
  one : Splitting -- unsplittable
  deeper : (pos : ℕ) -> Splitting -> Splitting -> Splitting


data Splitted (a : Ring') : Splitting -> Splitting → Set where
  one : (x : RC a) -> Splitted a one one
  empty : ∀ {r c} -> Splitted a r c
  quad : ∀ {r1 r2 c1 c2} -> ∀ m n -> Splitted a r1 c1 -> Splitted a r1 c2 -> Splitted a r2 c1 -> Splitted a r2 c2 -> 
            Splitted a (deeper m r1 r2) (deeper n c1 c2)


test : (a : Ring') -> Splitted a (deeper 1 one one) (deeper 1 one one)
test a = quad 1 1 empty (one (R0 a)) (one (R0 a)) empty 




flatTree : ℕ -> Bin
flatTree zero = empty
flatTree (suc n) = two empty (flatTree n)

size : Bin -> ℕ
size empty = 1
size (two y y') = size y + size y'

s∘fT≡suc : (n : ℕ) -> size (flatTree n) ≡ suc n
s∘fT≡suc zero = refl
s∘fT≡suc (suc n) = cong suc (s∘fT≡suc n)

Fsf->Fs : ∀ {n} -> Fin (size (flatTree n)) -> Fin (suc n) 
Fsf->Fs {n} f = subst Fin (s∘fT≡suc n) f


Fs->Fsf : ∀ {n} -> Fin (suc n) -> Fin (size (flatTree n))
Fs->Fsf {zero} x = x
Fs->Fsf {suc n} f0 = f0
Fs->Fsf {suc n} (fsuc i) = fsuc (Fs->Fsf {n} i)

-- borde kanske fixas
--Fs->Fs≡id : ∀ {n i} -> Fsf->Fs {suc n} (Fs->Fsf i) ≡ i
--Fs->Fs≡id = {!!}

embed : ∀ {a m n} -> AbMatrix a (suc m) (suc n) -> Rec a (flatTree m) 
                                                         (flatTree n) 
embed {a} {zero} {zero} mat = one (mat f0 f0)
embed {a} {suc m} {zero} mat = over (one (mat f0 f0)) 
                               (embed (λ i j → mat (fsuc i) j))
embed {a} {zero} {suc n} mat = side (one (mat f0 f0)) (embed (λ i j → mat i (fsuc j)))
embed {a} {suc m} {suc n} mat = side (over (one (mat f0 f0)) (embed (λ i j → mat (fsuc i) f0))) (embed (λ i j → mat i (fsuc j))) --side ({!embed!}) (embed (λ i j → mat i (fsuc j)))



proj : ∀ {a tr tc} -> Rec a tr tc -> AbMatrix a (size tr) (size tc)
proj (one x) = λ i j → x
proj {a} (side y y') = Ab++ a (proj y) (proj y')
proj {a} (over y y') = AbOver a (proj y) (proj y')
{-
agda : ∀ {a m n} -> AbMatrix a (suc m) (suc n) -> AbMatrix a (size (flatTree m)) (size (flatTree n))
agda {a} {m} {n} A with size∘flatTree≡suc m | inspect size∘flatTree≡suc m | size∘flatTree≡suc n | inspect size∘flatTree≡suc n
...| aa | ia | bb | bi = λ i j → A {!i!} {!!}
-}
-- agda-isom

--Goal: (Ab++ a (λ i' j' → A f0 f0)
--       (proj (embed (λ i' j' → A i' (fsuc j')))) i (Fs->Fsf j)
--       | (suc (toℕ (Fs->Fsf j)) ≤? suc 0 | toℕ (Fs->Fsf j) ≤? 0))
--      ≡ A i j

--lemma'' : ∀ a n (i : Fin 1) (j : Fin (suc n)) -> (A : AbMatrix a 1 (suc n)) -> proj (embed {a} (A)) (Fs->Fsf i) (Fs->Fsf j) ≡ A i j 
--lemma'' = {!!}

postulate 
  pf : ∀ a m n (i : Fin (suc m)) (j : Fin (suc n)) -> (A : AbMatrix a (suc m) (suc n)) -> proj (embed {a} (A)) (Fs->Fsf i) (Fs->Fsf j) ≡ A i j 

{-proj∘embed≡id : ∀ a m n (i : Fin (suc m)) (j : Fin (suc n)) -> (A : AbMatrix a (suc m) (suc n)) -> proj (embed {a} (A)) (Fs->Fsf i) (Fs->Fsf j) ≡ A i j 
proj∘embed≡id a zero zero f0 f0 A = refl
proj∘embed≡id a zero zero f0 (fsuc ()) A
proj∘embed≡id a zero zero (fsuc ()) j A
proj∘embed≡id a zero (suc n) i j A = {!!}
proj∘embed≡id a (suc m) n i j A = {!!}-}

-- splitable in 3 parts
data Tri (a : Ring') : Bin -> Set where
  one : Tri a empty
  trt : {t1 t2 : Bin} -> Tri a t1 -> Rec a t1 t2 -> Tri a t2 -> Tri a (two t1 t2)

--AbUTriang : Ring' -> ℕ -> ℕ -> ℕ -> Set
--AbUTriang = {!_,_!}
--IsTrianguar : (a : Ring') (m n d : ℕ) -> (A : AbMatrix a m n) -> Set

tembed : ∀ {a n} -> (A : AbMatrix a (suc n) (suc n)) -> IsTrianguar a 1 A -> Tri a (flatTree n) 
tembed {a} {zero} A pf = one
tembed {a} {suc n} A pf = trt one (embed {!!}) (tembed {a} {n} (λ i j → A (fsuc i) (fsuc j)) (λ i j x → pf (fsuc i) (fsuc j) {!!}))
-- vill ha:
--Data.Integer._≤_
--      (Data.Integer._+_ (+ 1) (Data.Integer._⊖_ (toℕ j) (toℕ i))) (+ 1)

-- 1 + (toℕ j - toℕ i) ≤ 1

-- har 
--Data.Integer._≤_
--     (Data.Integer._+_ (+ 1)
--      (Data.Integer._+_ (+ toℕ j) (Data.Integer.-_ (+ toℕ i)))) (+1)
-- 1 + (toℕ j) + (- toℕ i) ≤ 1


--proj : ∀ {a tr tc} -> Rec a tr tc -> AbMatrix a (size tr) (size tc)


tproj : ∀ {a t} -> Tri a t -> AbMatrix a (size t) (size t)
tproj = {!!}

-- tembed = tproj-inv
-- tproj utriang



-- tar A|B -> A*/B*
splitc : ∀ {a rt ct1 ct2} -> Rec a rt (two ct1 ct2) -> 
                             (Rec a rt ct1 × Rec a rt ct2)
splitc (side y y') = y , y'
splitc (over y y') = (over (proj₁ (splitc y)) (proj₁ (splitc y'))) , 
                      over (proj₂ (splitc y)) (proj₂ (splitc y'))

splitr : ∀{a rt1 rt2 ct} -> Rec a (two rt1 rt2) ct -> 
                            (Rec a rt1 ct × Rec a rt2 ct)
splitr (side y y') = (side (proj₁ (splitr y)) (proj₁ (splitr y'))) , 
                      side (proj₂ (splitr y)) (proj₂ (splitr y'))
splitr (over y y') = y , y'

rr+ : ∀ {a t1 t2} -> Rec a t1 t2 -> Rec a t1 t2 -> Rec a t1 t2
rr+ {a} (one x) (one x') = one (R+ a x x')
rr+ (side y y') (side y0 y1) = side (rr+ y y0) (rr+ y' y1)
rr+ (side y y') (over y0 y1) = side (rr+ y  (over (proj₁ (splitc y0)) 
                                                  (proj₁ (splitc y1)))) 
                                    (rr+ y' (over (proj₂ (splitc y0)) 
                                                  (proj₂ (splitc y1))))
--rr+ (side y y') (four y0 y1 y2 y3) = {!!}
rr+ (over y y') (side y0 y1) = side (rr+ (over (proj₁ (splitc y)) (proj₁ (splitc y'))) y0) (rr+ (over (proj₂ (splitc y)) (proj₂ (splitc y'))) y1)
rr+ (over y y') (over y0 y1) = over (rr+ y y0) (rr+ y' y1)
--rr+ (over y y') (four y0 y1 y2 y3) = {!!}
--rr+ (four y y' y0 y1) (side y2 y3) = {!!}
--rr+ (four y y' y0 y1) (over y2 y3) = {!!}
--rr+ (four y y' y0 y1) (four y2 y3 y4 y5) = four (rr+ y y2) (rr+ y' y3) (rr+ y0 y4) (rr+ y1 y5)
--rr+ (four y y' y0 y1) r2 = {!!}

tt+ : ∀ {a t1} -> Tri a t1 -> Tri a t1 -> Tri a t1
tt+ one one = one
tt+ (trt tr11 r1 tr12) (trt tr21 r2 tr22) = trt (tt+ tr11 tr21) (rr+ r1 r2) 
                                                                (tt+ tr12 tr22)



split4 : ∀ {a t1 t2 t3 t4} -> Rec a (two t1 t2) (two t3 t4) -> ((Rec a t1 t3 × Rec a t1 t4) × (Rec a t2 t3 × Rec a t2 t4))
split4 (side y y') = ((proj₁ (splitr y)) , (proj₁ (splitr y'))) , 
                      (proj₂ (splitr y)  ,  proj₂ (splitr y'))
split4 (over y y') = ((proj₁ (splitc y)) , (proj₂ (splitc y))) , 
                      (proj₁ (splitc y') ,  proj₂ (splitc y'))
-- en triangel är ett träd

rr* : ∀ {a t1 t2 t3} -> Rec a t1 t2 -> Rec a t2 t3 -> Rec a t1 t3
rr* {a} (one x) (one x') = one (R* a x x')
rr* (over y y') (one x) = over (rr* y (one x)) (rr* y' (one x))
rr* r1 (side y y') = side (rr* r1 y) (rr* r1 y')
rr* (side y y') (over y0 y1) = rr+ (rr* y y0) (rr* y' y1)
rr* (over y y') (over y0 y1) = over (rr* y (over y0 y1)) (rr* y' (over y0 y1))
{-
rr* {a} (one x) (one x') = one (R* a x x')
rr* (one x) (side y y') = side (rr* (one x) y) (rr* (one x) y')
rr* (side y y') (side y0 y1) = side {!rr* (side !} {!!}
rr* (side y y') (over y0 y1) = {!!}
rr* (over y y') r2 = {!!}-}

-- one x ger ett element!
rt* : ∀ {a t1 t2} -> Rec a t1 t2 -> Tri a t2 -> Rec a t1 t2
rt* {a} (one x) one = one (R0 a)
rt* (over y y') one = over (rt* y one) (rt* y' one) -- zero!
rt* (side y y') (trt y0 y1 y2) = side (rt* y y0) (rr+ (rr* y y1) (rt* y' y2))
rt* (over y y') (trt y0 y1 y2) = over (rt* y (trt y0 y1 y2)) (rt* y' (trt y0 y1 y2))
--rt* {a} (one x) one = one (Ring.0# a)
--rt* (side y y') (trt y0 y1 y2) = {!!}
--rt* (over y y') t = {!!}

tr* : ∀ {a t1 t2} -> Tri a t1 -> Rec a t1 t2 -> Rec a t1 t2
tr* {a} one (one x) = one (R0 a)
tr* one (side y y') = side (tr* one y) (tr* one y')
tr* (trt y y' y0) (side y1 y2) = side (tr* (trt y y' y0) y1) 
                                      (tr* (trt y y' y0) y2)
tr* (trt y y' y0) (over y1 y2) = over (rr+ (tr* y y1) (rr* y' y2)) (tr* y0 y2)

-- assumption: the triangles are transitively closed!!!
valiant : ∀ {a t1 t2} -> Tri a t1 -> Rec a t1 t2 -> Tri a t2 -> Rec a t1 t2
valiant one r one = r
valiant one (side y y') (trt y0 y1 y2) = rt* (side y y') (trt y0 y1 y2)
valiant (trt y y' y0) r one = tr* (trt y y' y0) r
valiant {a} (trt {u1} {u2} A₁ A₂ A₃) r (trt {l1} {l2} B₃ B₂ B₁) with split4 r 
...| (C₂ , C₄) , 
     (C₁ , C₃) = over (side X₂ X₄) 
                      (side X₁ X₃)
     where
     X₁ : Rec a u2 l1
     X₁ = valiant A₃ C₁ B₃
     X₂ : Rec a u1 l1
     X₂ = valiant A₁ (rr+ C₂ (rr* A₂ X₁)) B₃ -- not sure about this
     X₃ : Rec a u2 l2
     X₃ = valiant A₃ (rr+ C₃ (rr* X₁ B₂)) B₁ -- not sure about this
     X₄ : Rec a u1 l2
     X₄ = valiant A₁ (rr+ C₄ (rr+ (rr* A₂ X₃) (rr* X₂ B₂)) ) B₁ -- not sure

transclose : ∀ {a t1} -> Tri a t1 -> Tri a t1
transclose one = one
transclose (trt one C one) = trt one (valiant one C one) one
transclose (trt one C (trt B₃ B₂ B₁)) with transclose (trt B₃ B₂ B₁) 
...| B⁺ = trt one (rt* C B⁺) B⁺
transclose (trt (trt A₁ A₂ A₃) C one) with transclose (trt A₁ A₂ A₃)
...| A⁺ = trt A⁺ (tr* A⁺ C) one
transclose (trt (trt A₁ A₂ A₃) C (trt B₃ B₂ B₁)) with transclose (trt A₁ A₂ A₃) | transclose (trt B₃ B₂ B₁)
...                                                 | A⁺                        | B⁺                        = trt A⁺ (valiant A⁺ C B⁺) B⁺
--trt A₁⁺ A₂⁺ A₃⁺ | trt B₃⁺ B₂⁺ B₁⁺ = trt (trt A₁⁺ A₂⁺ A₃⁺) (valiant (trt A₁⁺ A₂⁺ A₃⁺) C (trt B₃⁺ B₂⁺ B₁⁺)) (trt B₃⁺ B₂⁺ B₁⁺)




-- summation : takes a sum thing, a function that creates, (hylomorphism, maybe)
sum : {a : Set} -> (plus : a -> a -> a) -> (gen : ℕ -> a) -> ℕ -> a
sum plus gen zero = gen zero
sum plus gen (suc n) = plus (gen (suc n)) (sum plus gen n)

-- pretty close to sum, sum with gen = if 0 then id else mat
--AbPow : {a : Set} -> (mul : a -> a -> a) -> a -> ℕ -> a
--AbPow mul mat zero = {!!}
--AbPow mul mat (suc n) = {!!}

matPow : ∀ a {n} -> AbMatrix a n n -> ℕ -> AbMatrix a n n
matPow a {n} mat = sum (AbMatrix* a) matGen
  where
  matGen : ℕ -> AbMatrix a n n
  matGen zero = AbId a n
  matGen (suc n') = mat

-- transitive closure is sum
transclosure : ∀ {a n} -> (A : AbMatrix a n n) -> IsTrianguar a 1 A -> 
                          AbMatrix a n n
transclosure {a} {n} A pf = sum (AbMatrix+ a) (matPow a A) n


