module Matrix.NewNewSplit where


open import Data.Nat
open import Data.Fin using (Fin; fromℕ; fromℕ≤; toℕ;  raise; reduce≥) 
                     renaming (zero to f0; suc to fsuc)

open import Data.Integer using (ℤ; +_; _-_)
open import Data.Vec renaming (Vec to SVec; [_] to <_>)
open import Matrix.Definitions using (toℤ) renaming (_≥_ to _z≥_; _<_ to _z<_)
open import Data.Empty
open import Algebra
open import Algebra.Structures
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Function
open import Relation.Nullary.Core

open Relation.Binary.PropositionalEquality.≡-Reasoning


open import Matrix.Abstract

f1 : ∀ {n} -> Fin (suc (suc n))
f1 = fsuc f0


data Splitting : Set where
  one : Splitting
  deeper  : Splitting -> Splitting -> Splitting


splitSize : Splitting -> ℕ
splitSize one = 1 
splitSize (deeper s1 s2) = splitSize s1 + splitSize s2


data SplitVec (a : Ring') : Splitting -> Set where
  one : (x : RC a) -> SplitVec a one
  two : ∀ {s1 s2} -> SplitVec a s1 -> SplitVec a s2 -> SplitVec a (deeper s1 s2)

zeroVec : ∀ {a s} -> SplitVec a s
zeroVec {a} {one} = one (R0 a)
zeroVec {a} {deeper s₁ s₂} = two (zeroVec {a} {s₁}) (zeroVec {a} {s₂})


-- or should one have a special construct for 1×1 matrixes?
data SplitMat (a : Ring') : Splitting -> Splitting -> Set where
  Sing : (x : RC a) -> SplitMat a one one
  RVec : ∀{s₁ s₂} -> SplitVec a (deeper s₁ s₂) -> SplitMat a one (deeper s₁ s₂)
  CVec : ∀{s₁ s₂} -> SplitVec a (deeper s₁ s₂) -> SplitMat a (deeper s₁ s₂) one
  quad : ∀{r1 r2 c1 c2} -> SplitMat a r1 c1 -> SplitMat a r1 c2 -> 
                           SplitMat a r2 c1 -> SplitMat a r2 c2 -> 
                           SplitMat a (deeper r1 r2) (deeper c1 c2)

sZero : ∀ {a s1 s2} -> SplitMat a s1 s2
sZero {a} {one} {one} = Sing (R0 a)
sZero {a} {one} {deeper y y'} = RVec zeroVec
sZero {a} {deeper y y'} {one} = CVec zeroVec
sZero {a} {deeper y y'} {deeper y0 y1} = quad sZero sZero sZero sZero 

projVec : ∀ a {s} -> SplitVec a s -> Vec a (splitSize s)
projVec a (one x) = λ i → x
projVec a (two y y') = V++ {a} (projVec a y) (projVec a y')

vecToRMat : ∀ {a n} -> Vec a n -> Matrix a 1 n
vecToRMat v = λ i j → v j

vecToCMat : ∀ {a n} -> Vec a n -> Matrix a n 1
vecToCMat v = λ i j → v i

splitToMat : ∀ a {rs cs} -> SplitMat a rs cs -> Matrix a (splitSize rs) (splitSize cs)
splitToMat a {one} {one} (Sing x) = λ _ _ → x 
splitToMat a {deeper y y'} {one} (CVec y0) = vecToCMat {a} (projVec a y0)
splitToMat a {one} {deeper y y'} (RVec y0) = vecToRMat {a} (projVec a y0)
splitToMat a {deeper y y'} {deeper y0 y1} (quad A B 
                                                C D) = Four a (splitToMat a A) (splitToMat a B) 
                                                              (splitToMat a C) (splitToMat a D)

simpleSplit : ℕ -> Splitting
simpleSplit zero = one
simpleSplit (suc n) = deeper one (simpleSplit n)

embedVec : ∀ a {n} -> Vec a (suc n) -> SplitVec a (simpleSplit n)
embedVec a {zero} v = one (v f0)
embedVec a {suc n} v = two (one (v f0)) (embedVec a (λ x → v (fsuc x)))

matToSplit : ∀ a {m n} -> Matrix a (suc m) (suc n) -> SplitMat a (simpleSplit m)
                                                                 (simpleSplit n)
--matToSplit a {zero} {zero} mat = CVec (one (mat f0 f0))
matToSplit a {zero} {zero} mat = Sing (mat f0 f0)
matToSplit a {suc n} {zero} mat = CVec (embedVec a (λ x → mat x f0))
matToSplit a {zero} {suc n} mat = RVec (embedVec a (λ x → mat f0 x))
matToSplit a {suc zero} {suc zero} mat = quad (Sing (mat f0 f0)) (Sing (mat f0 f1)) 
                                              (Sing (mat f1 f0)) (Sing (mat f1 f1))
matToSplit a {suc zero} {suc (suc n)} mat = quad (Sing (mat f0 f0)) (RVec (embedVec a (λ x → mat f0 (fsuc x)))) (Sing (mat f1 f0)) (RVec (embedVec a (λ x → mat f1 (fsuc x))))
matToSplit a {suc (suc n)} {suc zero} mat = quad (Sing (mat f0 f0)) (Sing (mat f0 f1)) (CVec (embedVec a (λ x → mat (fsuc x) f0))) (CVec (embedVec a (λ x → mat (fsuc x) f1)))
matToSplit a {suc (suc n)} {suc (suc n')} mat = quad (Sing (mat f0 f0)) (RVec (embedVec a (λ x → mat f0 (fsuc x)))) (CVec (embedVec a (λ x → mat (fsuc x) f0))) (matToSplit a (λ x x' → mat (fsuc x) (fsuc x'))) --quad {!!} {!!} {!!} {!!}


splitSize∘simpleSplit≡suc : (n : ℕ) -> splitSize (simpleSplit n) ≡ suc n 
splitSize∘simpleSplit≡suc zero = refl
splitSize∘simpleSplit≡suc (suc n) = cong suc (splitSize∘simpleSplit≡suc n)


injFin : ∀ {n} -> Fin (splitSize (simpleSplit n)) → Fin (suc n) 
injFin {zero} f0 = f0
injFin {zero} (fsuc i) = fsuc i
injFin {suc n} f0 = f0
injFin {suc n} (fsuc i) = fsuc (injFin {n} i)

outFin : ∀ {n} -> Fin (suc n) -> Fin (splitSize (simpleSplit n))
outFin {zero} f0 = f0
outFin {zero} (fsuc ())
outFin {suc n} f0 = f0
outFin {suc n} (fsuc i) = fsuc (outFin {n} i)

injFin∘outFin≡id : ∀ {n i} -> injFin (outFin {n} i) ≡ i
injFin∘outFin≡id {zero} {f0} = refl
injFin∘outFin≡id {zero} {fsuc ()}
injFin∘outFin≡id {suc n} {f0} = refl
injFin∘outFin≡id {suc n} {fsuc i} = cong fsuc injFin∘outFin≡id

outFin∘injFin≡id : ∀ {n i} -> outFin (injFin {n} i) ≡ i
outFin∘injFin≡id {zero} {f0} = refl
outFin∘injFin≡id {zero} {fsuc ()}
outFin∘injFin≡id {suc n} {f0} = refl
outFin∘injFin≡id {suc n} {fsuc i} = cong fsuc (outFin∘injFin≡id {n})

projEmbedVec≡id : (a : Ring') (m : ℕ) (i : Fin (splitSize (simpleSplit m))) -> (v : Vec a (suc m)) -> projVec a (embedVec a v) i ≡  v (injFin i)
projEmbedVec≡id a zero f0 v = refl
projEmbedVec≡id a zero (fsuc ()) v
projEmbedVec≡id a (suc n) f0 v = refl
projEmbedVec≡id a (suc n) (fsuc i) v = projEmbedVec≡id a n i (λ z → v (fsuc z))


splitToMat∘matToSplit≡id : (a : Ring') (m n : ℕ) (i : Fin (splitSize (simpleSplit m))) (j : Fin (splitSize (simpleSplit n))) -> (A : Matrix a (suc m) (suc n)) -> splitToMat a (matToSplit a A) i j ≡  A (injFin i) (injFin j)
splitToMat∘matToSplit≡id a zero zero f0 f0 A = refl
splitToMat∘matToSplit≡id a zero zero f0 (fsuc ()) A
splitToMat∘matToSplit≡id a zero zero (fsuc ()) j A
splitToMat∘matToSplit≡id a zero (suc n) f0 f0 A = refl
splitToMat∘matToSplit≡id a zero (suc n) f0 (fsuc i) A = projEmbedVec≡id a n i (λ x → A f0 (fsuc x))
splitToMat∘matToSplit≡id a zero (suc n) (fsuc ()) j A 
splitToMat∘matToSplit≡id a (suc n) zero f0 f0 A = refl
splitToMat∘matToSplit≡id a (suc n) zero f0 (fsuc ()) A
splitToMat∘matToSplit≡id a (suc n) zero (fsuc i) f0 A = projEmbedVec≡id a n i (λ x → A (fsuc x) f0)
splitToMat∘matToSplit≡id a (suc n) zero (fsuc i) (fsuc ()) A
splitToMat∘matToSplit≡id a (suc zero) (suc zero) f0 f0 A = refl
splitToMat∘matToSplit≡id a (suc zero) (suc (suc n)) f0 f0 A = refl
splitToMat∘matToSplit≡id a (suc (suc n)) (suc zero) f0 f0 A = refl
splitToMat∘matToSplit≡id a (suc (suc n)) (suc (suc n')) f0 f0 A = refl
splitToMat∘matToSplit≡id a (suc zero) (suc zero) f0 (fsuc f0) A = refl
splitToMat∘matToSplit≡id a (suc zero) (suc zero) f0 (fsuc (fsuc ())) A
splitToMat∘matToSplit≡id a (suc zero) (suc (suc n)) f0 (fsuc i) A = splitToMat∘matToSplit≡id a zero (suc n) f0 i
                                                                      (λ _ z → A f0 (fsuc z))
splitToMat∘matToSplit≡id a (suc (suc n)) (suc zero) f0 (fsuc i) A = splitToMat∘matToSplit≡id a zero zero f0 i (λ _ z → A f0 (fsuc z))
splitToMat∘matToSplit≡id a (suc (suc n)) (suc (suc n')) f0 (fsuc i) A = splitToMat∘matToSplit≡id a zero (suc n') f0 i
                                                                          (λ _ z → A f0 (fsuc z)) --lemma a n' i (λ z → A f0 (fsuc z))
splitToMat∘matToSplit≡id a (suc zero) (suc zero) (fsuc f0) f0 A = refl
splitToMat∘matToSplit≡id a (suc zero) (suc zero) (fsuc (fsuc ())) f0 A
splitToMat∘matToSplit≡id a (suc zero) (suc (suc n)) (fsuc f0) f0 A = refl
splitToMat∘matToSplit≡id a (suc zero) (suc (suc n)) (fsuc (fsuc ())) f0 A
splitToMat∘matToSplit≡id a (suc (suc n)) (suc zero) (fsuc f0) f0 A = refl
splitToMat∘matToSplit≡id a (suc (suc n)) (suc zero) (fsuc (fsuc i)) f0 A = projEmbedVec≡id a n i (λ x → A (fsuc (fsuc x)) f0) --Goal: projVec a (embedVec a (λ x → A (fsuc (fsuc x)) f0)) i ≡ A (fsuc (fsuc (injFin i))) f0
splitToMat∘matToSplit≡id a (suc (suc n)) (suc (suc n')) (fsuc f0) f0 A = refl
splitToMat∘matToSplit≡id a (suc (suc n)) (suc (suc n')) (fsuc (fsuc i)) f0 A = projEmbedVec≡id a n i (λ x → A (fsuc (fsuc x)) f0) -- projVec a (embedVec a (λ x → A (fsuc (fsuc x)) f0)) i ≡ A (fsuc (fsuc (injFin i))) f0
splitToMat∘matToSplit≡id a (suc zero) (suc zero) (fsuc f0) (fsuc f0) A = refl
splitToMat∘matToSplit≡id a (suc zero) (suc zero) (fsuc f0) (fsuc (fsuc ())) A
splitToMat∘matToSplit≡id a (suc zero) (suc zero) (fsuc (fsuc ())) (fsuc i) A
splitToMat∘matToSplit≡id a (suc (suc n)) (suc zero) (fsuc f0) (fsuc f0) A = refl
splitToMat∘matToSplit≡id a (suc (suc n)) (suc zero) (fsuc (fsuc i)) (fsuc f0) A = projEmbedVec≡id a n i (λ x → A (fsuc (fsuc x)) f1) -- Goal: projVec a (embedVec a (λ x → A (fsuc (fsuc x)) (fsuc f0))) i ≡ A (fsuc (fsuc (injFin i))) (fsuc f0)
splitToMat∘matToSplit≡id a (suc (suc n)) (suc zero) (fsuc i) (fsuc (fsuc ())) A
splitToMat∘matToSplit≡id a (suc zero) (suc (suc n')) (fsuc f0) (fsuc f0) A = refl
splitToMat∘matToSplit≡id a (suc zero) (suc (suc n')) (fsuc f0) (fsuc (fsuc i)) A = projEmbedVec≡id a n' i (λ x → A (fsuc f0) (fsuc (fsuc x))) --Goal: projVec a (embedVec a (λ x → A (fsuc f0) (fsuc (fsuc x)))) i ≡ A (fsuc f0) (fsuc (fsuc (injFin i)))
splitToMat∘matToSplit≡id a (suc zero) (suc (suc n')) (fsuc (fsuc ())) (fsuc i') A
splitToMat∘matToSplit≡id a (suc (suc n)) (suc (suc n')) (fsuc i) (fsuc i') A = splitToMat∘matToSplit≡id a (suc n) (suc n') i i'
                                                                                 (λ z z' → A (fsuc z) (fsuc z'))




splitToMat∘matToSplit≡id' : (a : Ring') (m n : ℕ) (i : Fin (suc m)) (j : Fin (suc n)) -> (A : Matrix a (suc m) (suc n)) -> splitToMat a (matToSplit a A) (outFin i) (outFin j) ≡  A i j 
splitToMat∘matToSplit≡id' a m n i j A = begin 
  splitToMat a (matToSplit a A) (outFin i) (outFin j) 
    ≡⟨ splitToMat∘matToSplit≡id a m n (outFin i) (outFin j) A ⟩ 
  A (injFin (outFin i)) (injFin (outFin j)) 
    ≡⟨ cong₂ A injFin∘outFin≡id injFin∘outFin≡id ⟩ 
  A i j ∎


splitVecAdd : ∀ {a rs} -> SplitVec a rs -> SplitVec a rs -> SplitVec a rs
splitVecAdd {a} {one} (one x) (one x') = one (R+ a x x')
splitVecAdd {a} {deeper s₁ s₂} (two v₁ v₂) (two u₁ u₂) = two (splitVecAdd v₁ u₁) (splitVecAdd v₂ v₂)

splitAdd : ∀ {a rs cs} -> SplitMat a rs cs -> SplitMat a rs cs -> SplitMat a rs cs
splitAdd {a} {one} {one} (Sing x) (Sing x') = Sing (R+ a x x')
splitAdd {a} {one} {deeper s₁ s₂} (RVec u) (RVec v) = RVec (splitVecAdd u v)
splitAdd {a} {deeper s₁ s₂} {one} (CVec u) (CVec v) = CVec (splitVecAdd u v)
splitAdd {a} {deeper s₁ s₂} {deeper t₁ t₂} (quad A₁ B₁ C₁ D₁) (quad A₂ B₂ C₂ D₂) = quad (splitAdd A₁ A₂) (splitAdd B₁ B₂) (splitAdd C₁ C₂) (splitAdd D₁ D₂)

splitDot : ∀ {a t1} -> SplitVec a t1 -> SplitVec a t1 -> RC a
splitDot {a} {one} (one x) (one x') = R* a x x'
splitDot {a} {deeper y y'} (two y0 y1) (two y2 y3) = R+ a (splitDot y0 y2) (splitDot y1 y3) --R+ a {!!} {!!}

-- |-----|---|   |-------|
-- |  A  | B | * |  C    |
-- |     |   |   |-------|  = A*C + B*D
-- |-----|---|   |- D----| 
scalarSplitVecMul : ∀ {a s} -> RC a -> SplitVec a s -> SplitVec a s
scalarSplitVecMul {a} x (one x') = one (R* a x x')
scalarSplitVecMul x (two y y') = two (scalarSplitVecMul x y) (scalarSplitVecMul x y')

splitVecScalarMul : ∀ {a s} -> SplitVec a s -> RC a -> SplitVec a s
splitVecScalarMul {a} (one x) x' = one (R* a x x')
splitVecScalarMul (two y y') x = two (splitVecScalarMul y x) (splitVecScalarMul y' x)

cVec : ∀ {a s} -> SplitVec a s -> SplitMat a s one
cVec {a} {one} (one x) = Sing x
cVec {a} {deeper y y'} v = CVec v
rVec : ∀ {a s} -> SplitVec a s -> SplitMat a one s
rVec {a} {one} (one x) = Sing x
rVec {a} {deeper y y'} v = RVec v

unMat1 : ∀ {a s} -> SplitMat a s one -> SplitVec a s
unMat1 (Sing x) = one x
unMat1 (CVec y) = y
unMat2 : ∀ {a s} -> SplitMat a one s -> SplitVec a s
unMat2 (Sing x) = one x
unMat2 (RVec y) = y


splitMatVecMul : ∀ {a t1 t2} -> SplitMat a t1 t2 -> SplitVec a t2 -> SplitVec a t1
splitMatVecMul {a} (Sing x) (one x') = one (R* a x x')
splitMatVecMul (RVec y) v = one (splitDot y v)
splitMatVecMul (CVec y) (one x) = splitVecScalarMul y x
splitMatVecMul (quad A B C D) (two v₁ v₂) = two (splitVecAdd (splitMatVecMul A v₁) (splitMatVecMul B v₂)) (splitVecAdd (splitMatVecMul C v₁) (splitMatVecMul D v₂))

splitVecMatMul : ∀ {a t1 t2} -> SplitVec a t1 -> SplitMat a t1 t2 -> SplitVec a t2
splitVecMatMul {a} (one x) (Sing x') = one (R* a x x')
splitVecMatMul (one x) (RVec y) = scalarSplitVecMul x y
splitVecMatMul u (CVec v) = one (splitDot u v) 
splitVecMatMul (two v₁ v₂) (quad A B C D) = two ( splitVecAdd (splitVecMatMul v₁ A) (splitVecMatMul v₂ C)) (splitVecAdd (splitVecMatMul v₁ B) (splitVecMatMul v₂ D))

splitMul : ∀ {a t1 t2 t3} -> SplitMat a t1 t2 -> SplitMat a t2 t3 -> SplitMat a t1 t3
splitMul {a} {one} {one} {one} (Sing x) (Sing x') = Sing (R* a x x')
splitMul {a} {one} {one} {deeper t₁ t₂} (Sing x) (RVec v) = RVec (scalarSplitVecMul x v)
splitMul {a} {deeper s₁ s₂} {one} (CVec y) (Sing x) = CVec (splitVecScalarMul y x)
splitMul {a} {deeper s₁ s₂} {one} {deeper t₁ t₂} (CVec (two u₁ u₂)) (RVec (two v₁ v₂)) = quad (splitMul (cVec u₁) (rVec v₁)) (splitMul (cVec u₁) (rVec v₂)) (splitMul (cVec u₂) (rVec v₁)) (splitMul (cVec u₂) (rVec v₂))
splitMul {a} {one} {deeper y y'} (RVec u) (CVec v) = Sing (splitDot u v)
splitMul {a} {one} {deeper y y'} (RVec (two u v)) (quad A B C D) = RVec (two (unMat2 (splitAdd (splitMul (rVec u) A) (splitMul (rVec v) C))) 
                                                                             (unMat2 (splitAdd (splitMul (rVec u) B) (splitMul (rVec v) D))))
splitMul {a} {deeper r1 r2} {deeper y y'} (quad A B C D) (CVec (two e f)) = CVec (two (unMat1 (splitAdd (splitMul A (cVec e)) (splitMul B (cVec f)))) 
                                                                                      (unMat1 (splitAdd (splitMul C (cVec e)) (splitMul D (cVec f)))))
splitMul {a} {deeper r1 r2} {deeper y y'} (quad A₁ B₁ C₁ D₁) (quad A₂ B₂ C₂ D₂) = quad (splitAdd (splitMul A₁ A₂) (splitMul B₁ C₂)) (splitAdd (splitMul A₁ B₂) (splitMul B₁ D₂)) (splitAdd (splitMul C₁ A₂) (splitMul D₁ C₂)) (splitAdd (splitMul C₁ B₂) (splitMul D₁ D₂))

-- properties needed: 
-- ok to lift add and mul

-- simple form: (sA -> A) & (sB -> B) => sA + sB -> A + B

-- if sA sA' -> A, sB sB' -> B then sA + sB 


-- kanske borde förenklas
{- COMMENTED OUT TO ALLOW INCLUSION
lift+ : ∀ a rs cs (sA sB : SplitMat a rs cs) (A B : Matrix a (splitSize rs) (splitSize cs)) -> (∀ i' j' -> (splitToMat a sA) i' j' ≡ A i' j') -> (∀ i' j' -> (splitToMat a sB) i' j' ≡ B i' j') -> (∀ i j -> (splitToMat a (splitAdd sA sB)) i j ≡ (Matrix+ a A B) i j)
lift+ a one one (Sing x) (Sing x') A B pfA pfB f0 f0 = cong₂ (R+ a) (pfA f0 f0) (pfB f0 f0)
lift+ a one one sA sB A B pfA pfB f0 (fsuc ())
lift+ a one one sA sB A B pfA pfB (fsuc ()) j
lift+ a one (deeper y y') sA sB A B pfA pfB i j = {!!}
lift+ a (deeper y y') one sA sB A B pfA pfB i j = {!!}
lift+ a (deeper y y') (deeper y0 y1) (quad y2 y3 y4 y5) (quad y6 y7 y8 y9) A B pfA pfB i j = {!!}
-- because then, it is possible to compute (A + B) by computing proj(embed(A) + embed(B))

--lift*
 


-}













-- mess:
-- 
--splitSize∘simpleSplit≡suc : ∀ {n} -> splitSize (simpleSplit n) ≡ suc n 
-- toℕ
--lemma''' : ∀ {m i} -> toℕ (injFin {m} i) ≡ toℕ (subst Fin (splitSize∘simpleSplit≡suc {m}) i)
--lemma''' m i = {!!}

{-
lemma'' : (m : ℕ) (i : Fin (splitSize (simpleSplit m))) -> injFin {m} i ≡ (subst Fin (splitSize∘simpleSplit≡suc m) i)
lemma'' zero i with simpleSplit zero 
lemma'' zero f0 | aa = refl
lemma'' zero (fsuc ()) | aa
lemma'' (suc zero) f0 = refl
lemma'' (suc (suc n)) f0 with suc (suc (suc n))
...| aa = {!!} --
--with (suc (suc n))--
--...| aa = {!!}


lemma'' (suc n) (fsuc i) with lemma'' n i 
...| aa = begin 
  fsuc (injFin i) 
    ≡⟨ cong fsuc aa ⟩ 
  fsuc (subst Fin (splitSize∘simpleSplit≡suc n) i)
    ≡⟨ {!!} ⟩  
  subst Fin (cong suc (splitSize∘simpleSplit≡suc n)) (fsuc i) ∎
-}
{-lemma'' (suc n) f0 with simpleSplit (suc n) | inspect simpleSplit (suc n)
...| aa | bb with splitSize aa | inspect splitSize aa | splitSize∘simpleSplit≡suc (suc n)
lemma'' (suc n) f0 | .(deeper one (simpleSplit n)) | [ refl ] | .(suc (splitSize (simpleSplit n))) | [ refl ] | ee with cong suc (splitSize∘simpleSplit≡suc n )
...| xxx = {!ee!}
lemma'' (suc n) (fsuc i) = {!!}-}
{-
lemma'' (suc n) i with simpleSplit (suc n) | inspect simpleSplit (suc n)
...| aa | dd with splitSize aa | inspect splitSize aa | splitSize∘simpleSplit≡suc (suc n)
lemma'' (suc n) i | one | [ () ] | .1 | [ refl ] | ee
lemma'' (suc n) i | deeper .one .(simpleSplit n) | [ refl ] | .(suc (splitSize (simpleSplit n))) | [ refl ] | ee = {!!}
-}

{-
lemma' : (a : Ring') (m n : ℕ) (i : Fin (splitSize (simpleSplit m))) (j : Fin (splitSize (simpleSplit n))) -> (A : Matrix a (suc m) (suc n)) -> A (injFin i) (injFin j) ≡ A i j
lemma' a m n i j A = cong₂ A (lemma'' m i) (lemma'' n j)-}