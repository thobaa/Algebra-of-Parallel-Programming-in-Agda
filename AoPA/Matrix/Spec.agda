module Matrix.Spec where

open import Matrix.Abstract
open import Matrix.Tri
open import Matrix.NewNewSplit
open import Data.Nat hiding (_⊓_)
open import Data.Product
open import Relation.Binary.PropositionalEquality
--open import Relation.Binary
open import Data.Fin using (Fin; fromℕ; fromℕ≤; toℕ;  raise; reduce≥) 
                     renaming (zero to f0; suc to fsuc)

open import Data.Unit
open import Level using () renaming (zero to Lzero)

open import Function

-- AOPA
open import Relations
open import Relations.Minimum
open import Relations.Coreflexive
open import Sets
open import AlgebraicReasoning.Relations

open import AlgebraicReasoning.Equality

-- summation: takes an addition operator, a generator and 
sum : {a : Set} -> (plus : a -> a -> a) -> (gen : ℕ -> a) -> ℕ -> a
sum plus gen zero = gen zero
sum plus gen (suc n) = plus (gen (suc n)) (sum plus gen n)

matPow : ∀ a {n} -> Matrix a n n -> ℕ -> Matrix a n n
matPow a {n} mat = sum (Matrix* a) matGen
  where
  matGen : ℕ -> Matrix a n n
  matGen zero = Id a n
  matGen (suc n') = mat


ttgen : ∀ {a s} -> Tri a s -> ℕ -> Tri a s
ttgen _ zero = tZero
ttgen mat (suc n) = mat

ttPow : ∀ a {s} -> Tri a s -> ℕ -> Tri a s
ttPow a {s} mat = sum ttmul (ttgen mat)

postulate 
  triangPf : ∀ {a} {da db m n p : ℕ} {A : Matrix a m n} {B : Matrix a n p} -> IsTriangular a da A -> IsTriangular a db B -> IsTriangular a (da + db) (Matrix* a A B)
 
-- is finite
sum-is-finite : {a : Set} -> (plus : a -> a -> a) -> (gen : ℕ -> a) -> Set
sum-is-finite plus gen = ∃ λ n → ∀ m → sum plus gen n ≡ sum plus gen (n + m)

-- example:
--∈ : {A : Set} → A ← ℙ A 
--∈ a s = s a 



-- need: relation on matrixes
-- for it, need relation on elements
postulate 
  ≤R : ∀ {R : Ring'} -> RC R ← RC R

-- Indexwise lifting of ≤R. (First matrix less than second.)
≤M : ∀ {a m n} -> (Matrix a m n) ← Matrix a m n
≤M {a = a} {m = m} {n = n} A B = (i : Fin m) (j : Fin n) → ≤R {a} (A i j) (B i j)

--matPow : ∀ a {n} -> Matrix a n n -> ℕ -> Matrix a n n
--sum : {a : Set} -> (plus : a -> a -> a) -> (gen : ℕ -> a) -> ℕ -> a
-- A is transitive closure of B (B not neccessarily triangular)
is-a-transitive-closure-of : ∀ {a n} -> Matrix a n n ← Matrix a n n
is-a-transitive-closure-of {a} A B = ∀ m → ≤M {a} (sum (Matrix+ a) (matPow a B) m) A


valiant-spec : ∀ {a} {n} -> Matrix a n n ← Matrix a n n
valiant-spec {a} {n} = min (is-a-transitive-closure-of {a} {n}) ₁∘ (IsTriangular {n} {n} a 1) ¿

triangular⇒finite-sum : ∀ {a n} -> (A : Matrix a n n) -> IsTriangular a 1 A -> sum-is-finite (Matrix+ a) (matPow a A)
triangular⇒finite-sum = {!!}


postulate 
  proj : ∀ {a s} -> Tri a s -> Matrix a (splitSize s) (splitSize s)

-- does that make sense?
postulate
  embed : ∀ {a s} -> Matrix a (splitSize s) (splitSize s) -> Tri a s





-- min of "transitive closures", nej, är argumentet som ska vara triangulärt
{-valiant-der : ∀ {a : Ring'} {n : ℕ} -> ∃ (λ f →  valiant-spec {a} {n} ⊒ fun (f {a} {n}) )
valiant-der {a} {n} = ({!!} , 
  (⊒-begin
    valiant-spec {a} {n}
      ⊒⟨ ⊒-refl ⟩
    min (is-a-transitive-closure-of {a} {n}) ₁∘ IsTriangular {n} {n} a 1 ¿
      ⊒⟨ {!!} ⟩ -- ← magic!
    fun (λ A → sum (Matrix+ a) (matPow a A) n) ○ IsTriangular {n} {n} a 1 ¿
    --  ⊒⟨ ⊒-refl ⟩
    --fun (λ A → id (sum (Matrix+ a) (matPow a A) n)) ○ IsTriangular {n} {n} a 1 ¿
      ⊒⟨ {!fun-comp!} ⟩
    fun (λ A → proj (sum ttadd (ttPow a (embed A)) n))
      ⊒⟨ {!fun-comp!} ⟩
    fun {!!}
      ⊒∎))
-}


-- idea: show that we get the finite sum below.
-- in it, introduce id before it, split id into putTogether∘takeApart
-- takeApart = (tri1, rect, tri2)  (takes matrix to respective part)
-- show that tri1, tri2 commutes with the sum.
-- show what happens with rect when moving it to other side.

-- transitive closure is sum
transclosure : ∀ {a n} -> (A : Matrix a n n) -> IsTriangular a 1 A -> Matrix a n n
transclosure {a} {n} A pf = sum (Matrix+ a) (matPow a A) n


≤V : ∀ {a s} -> SplitVec a s ← SplitVec a s
≤V {a} {one} (one x) (one x') = ≤R {a} x x'
≤V {a} {deeper y y'} (two y0 y1) (two y2 y3) = ≤V {a} y0 y2 × ≤V {a} y1 y3

≤S : ∀ {a s1 s2} -> SplitMat a s1 s2 ← SplitMat a s1 s2
≤S {a} {one} {one} (Sing x) (Sing x') = ≤R {a} x x'
≤S {a} {one} {deeper y y'} (RVec y0) (RVec y1) = ≤V y0 y1
≤S {a} {deeper y y'} {one} (CVec y0) (CVec y1) = ≤V y0 y1
≤S {a} {deeper y y'} {deeper y0 y1} (quad y2 y3 y4 y5) (quad y6 y7 y8 y9) = ≤S y2 y6 × ≤S y3 y7 × ≤S y4 y8 × ≤S y5 y9

-- doing the stuff for triangs:
≤T : ∀ {a s} -> Tri a s ← Tri a s
≤T {a} {one} one one = ⊤
≤T {a} {deeper s1 s2} (two y0 y1 y2) (two y3 y4 y5) = (≤T y0 y3 × ≤S y1 y4 × ≤T y2 y5)

Tis-a-transitive-closure-of : ∀ {a s} -> Tri a s ← Tri a s
Tis-a-transitive-closure-of {a} A B = ∀ m → ≤T {a} (sum (ttadd) (ttPow a B) m) A


tri1-ttadd-commute : ∀ {a s1 s2} → (T₁ : Tri a (deeper s1 s2)) -> (T₂ : Tri a (deeper s1 s2)) → tri1 (ttadd T₁ T₂) ≡ ttadd (tri1 T₁) (tri1 T₂)
tri1-ttadd-commute (two y y' y0) (two y1 y2 y3) = refl

tri1-ttmul-commute : ∀ {a s1 s2} → (T₁ : Tri a (deeper s1 s2)) -> (T₂ : Tri a (deeper s1 s2)) → tri1 (ttmul T₁ T₂) ≡ ttmul (tri1 T₁) (tri1 T₂)
tri1-ttmul-commute (two y y' y0) (two y1 y2 y3) = refl

tri1-pow-commute : ∀ {a s1 s2} n → (T : Tri a (deeper s1 s2)) -> tri1 (ttPow a T n) ≡ ttPow a (tri1 T) n
tri1-pow-commute zero T = refl
tri1-pow-commute (suc n) T = ≡-begin 
  tri1 (ttmul T (sum ttmul (ttgen T) n)) 
  ≡⟨ tri1-ttmul-commute T (sum ttmul (ttgen T) n) ⟩ 
  ttmul (tri1 T) (tri1 (sum ttmul (ttgen T) n)) 
  ≡⟨ cong (λ x → ttmul (tri1 T) x) (tri1-pow-commute n T) ⟩ 
  ttmul (tri1 T) (sum ttmul (ttgen (tri1 T)) n) ≡∎

T-sum-pow : ∀ {a s} -> Tri a s -> Tri a s
T-sum-pow {a} {s} A = sum ttadd (ttPow a A) (splitSize s)

tri1-T-sum-pow-commute' : ∀ {a s1 s2 n} -> (T : Tri a (deeper s1 s2)) -> tri1 (sum ttadd (ttPow a T) n) ≡ sum ttadd (ttPow a (tri1 T)) n
tri1-T-sum-pow-commute' {a} {s1} {s2} {zero} (two T₁ R T₂) = refl
tri1-T-sum-pow-commute' {a} {s1} {s2} {suc n} (two T₁ R T₂) = ≡-begin 
  tri1
    (ttadd (ttmul (two T₁ R T₂) (sum ttmul (ttgen (two T₁ R T₂)) n))
     (sum ttadd (sum ttmul (ttgen (two T₁ R T₂))) n))
  ≡⟨ tri1-ttadd-commute (ttmul (two T₁ R T₂) (sum ttmul (ttgen (two T₁ R T₂)) n)) (sum ttadd (sum ttmul (ttgen (two T₁ R T₂))) n) ⟩
  ttadd
    (tri1 (ttmul (two T₁ R T₂) (sum ttmul (ttgen (two T₁ R T₂)) n)))
    (tri1 (sum ttadd (sum ttmul (ttgen (two T₁ R T₂))) n))
  ≡⟨ cong (λ x → ttadd x (tri1 (sum ttadd (sum ttmul (ttgen (two T₁ R T₂))) n))) (tri1-ttmul-commute (two T₁ R T₂) (sum ttmul (ttgen (two T₁ R T₂)) n)) ⟩
  ttadd
    (ttmul T₁ (tri1 (sum ttmul (ttgen (two T₁ R T₂)) n)))
    (tri1 (sum ttadd (sum ttmul (ttgen (two T₁ R T₂))) n))
  ≡⟨ cong (λ x → ttadd (ttmul T₁ x)
                   (tri1 (sum ttadd (sum ttmul (ttgen (two T₁ R T₂))) n))) (tri1-pow-commute n (two T₁ R T₂)) ⟩
  ttadd
    (ttmul T₁ (sum ttmul (ttgen (tri1 (two T₁ R T₂))) n))
    (tri1 (sum ttadd (sum ttmul (ttgen (two T₁ R T₂))) n))
  ≡⟨ refl ⟩
  ttadd
    (ttmul T₁ (sum ttmul (ttgen T₁) n))
    (tri1 (sum ttadd (sum ttmul (ttgen (two T₁ R T₂))) n))
  ≡⟨ cong (λ x → ttadd (ttmul T₁ (sum ttmul (ttgen T₁) n)) x) (tri1-T-sum-pow-commute' {a} {s1} {s2} {n} (two T₁ R T₂)) ⟩
  ttadd (ttmul T₁ (sum ttmul (ttgen T₁) n))
    (sum ttadd (sum ttmul (ttgen T₁)) n) ≡∎




tri1-T-sum-pow-commute : ∀ {a s1 s2} -> (T : Tri a (deeper s1 s2)) -> tri1 (T-sum-pow T) ≡ T-sum-pow (tri1 T)
tri1-T-sum-pow-commute {a} {s1} {s2} (two T₁ R T₂) = ≡-begin 
  tri1
    (sum ttadd (sum ttmul (ttgen (two T₁ R T₂)))
     (splitSize s1 + splitSize s2)) 
    ≡⟨ tri1-T-sum-pow-commute' {a} {s1} {s2} {splitSize s1 + splitSize s2} (two T₁ R T₂) ⟩ 
  sum ttadd (sum ttmul (ttgen (tri1 (two T₁ R T₂)))) (splitSize s1 + splitSize s2)
    ≡⟨ refl ⟩ 
  sum ttadd (sum ttmul (ttgen T₁)) (splitSize s1 + splitSize s2)
    ≡⟨ {!!} ⟩ -- the last s2 are 0
  sum ttadd (sum ttmul (ttgen T₁)) (splitSize s1) ≡∎

-- same as tri1-T-...
tri2-T-sum-pow-commute : ∀ {a s1 s2} -> (T : Tri a (deeper s1 s2)) -> tri2 (T-sum-pow T) ≡ T-sum-pow (tri2 T)
tri2-T-sum-pow-commute = {!!}



-- or maybe define trt-mul?
rec-T-sum-pow-kind-of-commute : {a : Ring'} {s1 s2 : Splitting} {T : Tri a (deeper s1 s2)} -> rec {a} {s1} {s2} (sum ttadd (sum ttmul (ttgen T)) (splitSize s1 + splitSize s2)) ≡ 
                                                                                                                trmul (sum ttadd (sum ttmul (ttgen (tri1 T))) (splitSize s1))
                                                                                                                      (rtmul (rec T) (sum ttadd (sum ttmul (ttgen (tri2 T))) (splitSize s2)))
rec-T-sum-pow-kind-of-commute {a} {s1} {s2} {T} = {!!}




valiant-der' : ∀ {a : Ring'} {s1 s2  : Splitting} -> ∃ (λ f → min ≤T ₁∘ (Tis-a-transitive-closure-of {a} {deeper s1 s2}) ⊒ fun f )
valiant-der' {a} {s1} {s2} = ({!!} , 
  (⊒-begin
    min ≤T ₁∘ (Tis-a-transitive-closure-of {a} {deeper s1 s2})
      ⊒⟨ {!!} ⟩ -- ← magic!
  fun T-sum-pow
        ⊒⟨ ⊒-refl ⟩
  fun (id T-sum-pow)
        ⊒⟨ (λ b a' x → {!!}) ⟩
  fun (unsplit ∘ split ∘ T-sum-pow)
        ⊒⟨ ⊒-refl ⟩
  fun (unsplit ∘ ⟨ tri1 , rec , tri2 ⟩ ∘ T-sum-pow)
        ⊒⟨ ⊒-refl ⟩
  fun (unsplit ∘ ⟨ tri1  ∘ T-sum-pow , rec ∘ T-sum-pow , tri2  ∘ T-sum-pow ⟩)
        ⊒⟨ (λ b a' x → ≡-begin 
                         two
                           (tri1
                            (sum ttadd (sum ttmul (ttgen a')) (splitSize s1 + splitSize s2)))
                           (rec
                            (sum ttadd (sum ttmul (ttgen a')) (splitSize s1 + splitSize s2)))
                           (tri2
                            (sum ttadd (sum ttmul (ttgen a')) (splitSize s1 + splitSize s2)))
                         ≡⟨ cong₂ (λ x' y' → two x' (rec
                                                   (sum ttadd (sum ttmul (ttgen a')) (splitSize s1 + splitSize s2))) y') (tri1-T-sum-pow-commute a') (tri2-T-sum-pow-commute a') ⟩
                         two 
                           (sum ttadd (sum ttmul (ttgen (tri1 a'))) (splitSize s1))
                           (rec
                            (sum ttadd (sum ttmul (ttgen a')) (splitSize s1 + splitSize s2)))
                           (sum ttadd (sum ttmul (ttgen (tri2 a'))) (splitSize s2))
                         ≡⟨ x ⟩
                         b ≡∎) ⟩
  fun (unsplit ∘ ⟨ T-sum-pow ∘ tri1 , rec ∘ T-sum-pow , T-sum-pow ∘ tri2 ⟩)
        ⊒⟨ (λ b a' z → z) ⟩
  fun (let A' = T-sum-pow ∘ tri1 
           B' = T-sum-pow ∘ tri2 in unsplit ∘ ⟨ A' , rec ∘ T-sum-pow  , B' ⟩)
        ⊒⟨ (λ b a' x → ≡-begin 
                       two (sum ttadd (sum ttmul (ttgen (tri1 a'))) (splitSize s1)) (rec (sum ttadd (sum ttmul (ttgen a')) (splitSize s1 + splitSize s2)))
                                                                                    (sum ttadd (sum ttmul (ttgen (tri2 a'))) (splitSize s2)) 
                       ≡⟨ cong (λ x' → two (sum ttadd (sum ttmul (ttgen (tri1 a'))) (splitSize s1)) x'
                                                                                                    (sum ttadd (sum ttmul (ttgen (tri2 a'))) (splitSize s2))) 
                          rec-T-sum-pow-kind-of-commute ⟩ 
                       two (sum ttadd (sum ttmul (ttgen (tri1 a'))) (splitSize s1)) (trmul (sum ttadd (sum ttmul (ttgen (tri1 a'))) (splitSize s1))
                                                                                      (rtmul (rec a')
                           (sum ttadd (sum ttmul (ttgen (tri2 a'))) (splitSize s2))))
                         (sum ttadd (sum ttmul (ttgen (tri2 a'))) (splitSize s2))
                       ≡⟨ x ⟩ 
                       b ≡∎) ⟩
  fun (let A' = T-sum-pow ∘ tri1 
           B' = T-sum-pow ∘ tri2 in unsplit ∘ ⟨ A' , (λ x → trmul (A' x) (rtmul (rec x) (B' x))) , B' ⟩) -- what about non-associativity???
        ⊒⟨ {!!} ⟩
  fun valiant
      ⊒∎))