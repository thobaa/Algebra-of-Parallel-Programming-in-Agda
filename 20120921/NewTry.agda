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
--open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Function
open import Relation.Nullary.Core

open import Relation.Binary.HeterogeneousEquality using (_≅_; ≡-to-≅)
open Relation.Binary.HeterogeneousEquality.≅-Reasoning
--open Relation.Binary.PropositionalEquality.≡-Reasoning (_≅_)

open import Abstract

data Bin : Set where
  empty : Bin
  two   : Bin  -> Bin -> Bin


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
  deeper : Splitting -> Splitting -> Splitting -- what does pos do here?


data Splitted (a : Ring') : Splitting -> Splitting → Set where
  one : (x : RC a) -> Splitted a one one
  empty : ∀ {r c} -> Splitted a r c -- either no extent, or zeros. => need ring
  quad : ∀ {r1 r2 c1 c2} -> Splitted a r1 c1 -> Splitted a r1 c2 -> 
                            Splitted a r2 c1 -> Splitted a r2 c2 -> Splitted a (deeper r1 r2) (deeper c1 c2)

Ssize : Splitting -> ℕ
Ssize empty = 0
Ssize one = 1
Ssize (deeper y y') = Ssize y + Ssize y'

splittedProj : ∀ {a rs cs} -> Splitted a rs cs -> Matrix a (Ssize rs) (Ssize cs)
splittedProj (one x) = λ i j → x
splittedProj {a} (empty {rs} {cs}) = λ i j → R0 a
splittedProj (quad A B 
                    C D) = {!!}

sFlatTree : ℕ -> Splitting
sFlatTree zero = empty
--sFlatTree (suc zero) = one
sFlatTree (suc n) = deeper one (sFlatTree n)

splittedEmbedRVec : ∀ {a n} -> Vec a n -> Splitted a one (sFlatTree n)
splittedEmbedRVec = {!!} 

splittedEmbedCVec : ∀ {a n} -> Vec a n -> Splitted a (sFlatTree n) one
splittedEmbedCVec = {!!} 



splittedEmbed : ∀ {a m n} -> Matrix a m n -> Splitted a (sFlatTree m) (sFlatTree n)
splittedEmbed {a} {zero} {n} A = empty
splittedEmbed {a} {suc n} {zero} A = empty
splittedEmbed {a} {suc m} {suc n} A = quad (one (A f0 f0)) (splittedEmbedRVec (λ x → A f0 (fsuc x))) (splittedEmbedCVec (λ x → A (fsuc x) f0)) (splittedEmbed (λ i j → A (fsuc i) (fsuc j)))

splitProjEmbed≡Id : ∀ a m n (A : Matrix a m n) -> splittedProj {a} (splittedEmbed {a} A) ≅ A
splitProjEmbed≡Id a zero n A = begin 
                               splittedProj {a} (splittedEmbed {a} A) 
                                 ≅⟨ {!Extensionality ? ?!} ⟩ -- or applying
                               A ∎
splitProjEmbed≡Id a (suc n) n' A = {!!}

test : (a : Ring') -> Splitted a (deeper one one) (deeper one one)
test a = quad empty (one (R0 a)) (one (R0 a)) empty 




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

embed : ∀ {a m n} -> Matrix a (suc m) (suc n) -> Rec a (flatTree m) 
                                                         (flatTree n) 
embed {a} {zero} {zero} mat = one (mat f0 f0)
embed {a} {suc m} {zero} mat = over (one (mat f0 f0)) 
                               (embed (λ i j → mat (fsuc i) j))
embed {a} {zero} {suc n} mat = side (one (mat f0 f0)) (embed (λ i j → mat i (fsuc j)))
embed {a} {suc m} {suc n} mat = side (over (one (mat f0 f0)) (embed (λ i j → mat (fsuc i) f0))) (embed (λ i j → mat i (fsuc j))) --side ({!embed!}) (embed (λ i j → mat i (fsuc j)))



proj : ∀ {a tr tc} -> Rec a tr tc -> Matrix a (size tr) (size tc)
proj (one x) = λ i j → x
proj {a} (side y y') = ++ a (proj y) (proj y')
proj {a} (over y y') = Over a (proj y) (proj y')
{-
agda : ∀ {a m n} -> Matrix a (suc m) (suc n) -> Matrix a (size (flatTree m)) (size (flatTree n))
agda {a} {m} {n} A with size∘flatTree≡suc m | inspect size∘flatTree≡suc m | size∘flatTree≡suc n | inspect size∘flatTree≡suc n
...| aa | ia | bb | bi = λ i j → A {!i!} {!!}
-}
-- agda-isom

--Goal: (++ a (λ i' j' → A f0 f0)
--       (proj (embed (λ i' j' → A i' (fsuc j')))) i (Fs->Fsf j)
--       | (suc (toℕ (Fs->Fsf j)) ≤? suc 0 | toℕ (Fs->Fsf j) ≤? 0))
--      ≡ A i j

--lemma'' : ∀ a n (i : Fin 1) (j : Fin (suc n)) -> (A : Matrix a 1 (suc n)) -> proj (embed {a} (A)) (Fs->Fsf i) (Fs->Fsf j) ≡ A i j 
--lemma'' = {!!}

--postulate 
--  pf : ∀ a m n (i : Fin (suc m)) (j : Fin (suc n)) -> (A : Matrix a (suc m) (suc n)) -> proj (embed {a} (A)) (Fs->Fsf i) (Fs->Fsf j) ≡ A i j 

{-proj∘embed≡id : ∀ a m n (i : Fin (suc m)) (j : Fin (suc n)) -> (A : Matrix a (suc m) (suc n)) -> proj (embed {a} (A)) (Fs->Fsf i) (Fs->Fsf j) ≡ A i j 
proj∘embed≡id a zero zero f0 f0 A = refl
proj∘embed≡id a zero zero f0 (fsuc ()) A
proj∘embed≡id a zero zero (fsuc ()) j A
proj∘embed≡id a zero (suc n) i j A = {!!}
proj∘embed≡id a (suc m) n i j A = {!!}-}

-- splitable in 3 parts
data Tri (a : Ring') : Bin -> Set where
  one : Tri a empty
  trt : {t1 t2 : Bin} -> Tri a t1 -> Rec a t1 t2 -> Tri a t2 -> Tri a (two t1 t2)

--UTriang : Ring' -> ℕ -> ℕ -> ℕ -> Set
--UTriang = {!_,_!}
--IsTriangular : (a : Ring') (m n d : ℕ) -> (A : Matrix a m n) -> Set

tembed : ∀ {a n} -> (A : Matrix a (suc n) (suc n)) -> IsTriangular a 1 A -> Tri a (flatTree n) 
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


--proj : ∀ {a tr tc} -> Rec a tr tc -> Matrix a (size tr) (size tc)


tproj : ∀ {a t} -> Tri a t -> Matrix a (size t) (size t)
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




