import Matrix.Abstract
import Matrix.Tri
import Matrix.NewNewSplit
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

-- END AOPA
open import Level using () renaming (zero to Lzero)

open import Matrix.NonAssociativeRing

module Matrix.Spec (NAR : NonAssociativeRing Lzero Lzero) where

open Matrix.Abstract (NAR)
open Matrix.Tri (NAR)
open Matrix.NewNewSplit (NAR)


-- summation: takes an addition operator, a generator and 
sum : {a : Set} -> (plus : a -> a -> a) -> (gen : ℕ -> a) -> ℕ -> a
sum plus gen zero = gen zero
sum plus gen (suc n) = plus (gen (suc n)) (sum plus gen n)


matPow : ∀ {n} -> Matrix n n -> ℕ -> Matrix n n
matPow {n} mat = sum (_M*_) matGen
  where
  matGen : ℕ -> Matrix n n
  matGen zero = {!!}
  matGen (suc n') = mat


ttgen : ∀ {s} -> Tri s -> ℕ -> Tri s
ttgen _ zero = T0
ttgen mat (suc n) = mat

ttPow : ∀ {s} -> Tri s -> ℕ -> Tri s
ttPow {s} mat = sum _T*_ (ttgen mat)

postulate 
  triangPf : ∀ {da db m n p : ℕ} {A : Matrix m n} {B : Matrix n p} -> IsTriangular da A -> IsTriangular db B -> IsTriangular (da + db) (A M* B)
 
-- is finite
sum-is-finite : {a : Set} -> (plus : a -> a -> a) -> (gen : ℕ -> a) -> Set
sum-is-finite plus gen = ∃ λ n → ∀ m → sum plus gen n ≡ sum plus gen (n + m)

-- example:
--∈ : {A : Set} → A ← ℙ A 
--∈ a s = s a 



-- need: relation on matrixes
-- for it, need relation on elements
postulate 
  ≤R : R ← R

-- Indexwise lifting of ≤R. (First matrix less than second.)
≤M : ∀ {m n} -> (Matrix m n) ← Matrix m n
≤M {m = m} {n = n} A B = (i : Fin m) (j : Fin n) → ≤R (A i j) (B i j)

--matPow : ∀ a {n} -> Matrix a n n -> ℕ -> Matrix a n n
--sum : {a : Set} -> (plus : a -> a -> a) -> (gen : ℕ -> a) -> ℕ -> a
-- A is transitive closure of B (B not neccessarily triangular)
is-a-transitive-closure-of : ∀ {n} -> Matrix n n ← Matrix n n
is-a-transitive-closure-of A B = ∀ m → ≤M (sum (_M+_) (matPow B) m) A


valiant-spec : ∀ {n} -> Matrix n n ← Matrix n n
valiant-spec {n} = min (is-a-transitive-closure-of {n}) ₁∘ (IsTriangular {n} {n} 1) ¿

triangular⇒finite-sum : ∀ {n} -> (A : Matrix n n) -> IsTriangular 1 A -> sum-is-finite (_M+_) (matPow A)
triangular⇒finite-sum = {!!}


postulate 
  proj : ∀ {s} -> Tri s -> Matrix (splitSize s) (splitSize s)

-- does that make sense?
postulate
  embed : ∀ {s} -> Matrix (splitSize s) (splitSize s) -> Tri s





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
    fun (λ A → proj (sum _T+_ (ttPow a (embed A)) n))
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
transclosure : ∀ {n} -> (A : Matrix n n) -> IsTriangular 1 A -> Matrix n n
transclosure {n} A pf = sum (_M+_) (matPow A) n


≤V : ∀ {s} -> SplitVec s ← SplitVec s
≤V {one} (one x) (one x') = ≤R x x'
≤V {deeper y y'} (two y0 y1) (two y2 y3) = ≤V y0 y2 × ≤V y1 y3

≤S : ∀ {s1 s2} -> SplitMat s1 s2 ← SplitMat s1 s2
≤S {one} {one} (Sing x) (Sing x') = ≤R x x'
≤S {one} {deeper y y'} (RVec y0) (RVec y1) = ≤V y0 y1
≤S {deeper y y'} {one} (CVec y0) (CVec y1) = ≤V y0 y1
≤S {deeper y y'} {deeper y0 y1} (quad y2 y3 y4 y5) (quad y6 y7 y8 y9) = ≤S y2 y6 × ≤S y3 y7 × ≤S y4 y8 × ≤S y5 y9

-- doing the stuff for triangs:
≤T : ∀ {s} -> Tri s ← Tri s
≤T {one} one one = ⊤
≤T {deeper s1 s2} (two y0 y1 y2) (two y3 y4 y5) = (≤T y0 y3 × ≤S y1 y4 × ≤T y2 y5)

Tis-a-transitive-closure-of : ∀ {s} -> Tri s ← Tri s
Tis-a-transitive-closure-of A B = ∀ m → ≤T (sum (_T+_) (ttPow B) m) A


tri1-T+-commute : ∀ {s1 s2} → (T₁ : Tri (deeper s1 s2)) -> (T₂ : Tri (deeper s1 s2)) → tri1 (T₁ T+ T₂) ≡ (tri1 T₁) T+ (tri1 T₂)
tri1-T+-commute (two y y' y0) (two y1 y2 y3) = refl

tri1-T*-commute : ∀ {s1 s2} → (T₁ : Tri (deeper s1 s2)) -> (T₂ : Tri (deeper s1 s2)) → tri1 (T₁ T* T₂) ≡ (tri1 T₁) T* (tri1 T₂)
tri1-T*-commute (two y y' y0) (two y1 y2 y3) = refl

tri1-pow-commute : ∀ {s1 s2} n → (T : Tri (deeper s1 s2)) -> tri1 (ttPow T n) ≡ ttPow (tri1 T) n
tri1-pow-commute zero T = refl
tri1-pow-commute (suc n) T = ≡-begin 
  tri1 (T T* (sum _T*_ (ttgen T) n)) 
  ≡⟨ tri1-T*-commute T (sum _T*_ (ttgen T) n) ⟩ 
  (tri1 T) T* (tri1 (sum _T*_ (ttgen T) n)) 
  ≡⟨ cong (λ x → (tri1 T) T* x) (tri1-pow-commute n T) ⟩ 
  (tri1 T) T* (sum _T*_ (ttgen (tri1 T)) n) ≡∎

T-sum-pow : ∀ {s} -> Tri s -> Tri s
T-sum-pow {s} A = sum _T+_ (ttPow A) (splitSize s)

tri1-T-sum-pow-commute' : ∀ {s1 s2 n} -> (T : Tri (deeper s1 s2)) -> tri1 (sum _T+_ (ttPow T) n) ≡ sum _T+_ (ttPow (tri1 T)) n
tri1-T-sum-pow-commute' {s1} {s2} {zero} (two T₁ R T₂) = refl
tri1-T-sum-pow-commute' {s1} {s2} {suc n} (two T₁ R T₂) = ≡-begin 
  tri1
    (((two T₁ R T₂) T* (sum _T*_ (ttgen (two T₁ R T₂)) n)) T+
     (sum _T+_ (sum _T*_ (ttgen (two T₁ R T₂))) n))
  ≡⟨ tri1-T+-commute ((two T₁ R T₂) T* (sum _T*_ (ttgen (two T₁ R T₂)) n)) (sum _T+_ (sum _T*_ (ttgen (two T₁ R T₂))) n) ⟩
  (tri1 ((two T₁ R T₂) T* (sum _T*_ (ttgen (two T₁ R T₂)) n))) 
    T+
  (tri1 (sum _T+_ (sum _T*_ (ttgen (two T₁ R T₂))) n))
  ≡⟨ cong (λ x → x T+ (tri1 (sum _T+_ (sum _T*_ (ttgen (two T₁ R T₂))) n))) (tri1-T*-commute (two T₁ R T₂) (sum _T*_ (ttgen (two T₁ R T₂)) n)) ⟩
  (T₁ T* (tri1 (sum _T*_ (ttgen (two T₁ R T₂)) n)))
    T+
  (tri1 (sum _T+_ (sum _T*_ (ttgen (two T₁ R T₂))) n))
  ≡⟨ cong (λ x → (T₁ T* x) T+ (tri1 (sum _T+_ (sum _T*_ (ttgen (two T₁ R T₂))) n))) (tri1-pow-commute n (two T₁ R T₂)) ⟩
  (T₁ T* (sum _T*_ (ttgen (tri1 (two T₁ R T₂))) n))
    T+
  (tri1 (sum _T+_ (sum _T*_ (ttgen (two T₁ R T₂))) n))
  ≡⟨ refl ⟩
  (T₁ T* (sum _T*_ (ttgen T₁) n))
    T+
  (tri1 (sum _T+_ (sum _T*_ (ttgen (two T₁ R T₂))) n))
  ≡⟨ cong (λ x → (T₁ T* (sum _T*_ (ttgen T₁) n)) T+ x) (tri1-T-sum-pow-commute' {s1} {s2} {n} (two T₁ R T₂)) ⟩
  (T₁ T* (sum _T*_ (ttgen T₁) n)) T+ (sum _T+_ (sum _T*_ (ttgen T₁)) n) 
  ≡∎




tri1-T-sum-pow-commute : ∀ {s1 s2} -> (T : Tri (deeper s1 s2)) -> tri1 (T-sum-pow T) ≡ T-sum-pow (tri1 T)
tri1-T-sum-pow-commute {s1} {s2} (two T₁ R T₂) = ≡-begin 
  tri1
    (sum _T+_ (sum _T*_ (ttgen (two T₁ R T₂)))
     (splitSize s1 + splitSize s2)) 
    ≡⟨ tri1-T-sum-pow-commute' {s1} {s2} {splitSize s1 + splitSize s2} (two T₁ R T₂) ⟩ 
  sum _T+_ (sum _T*_ (ttgen (tri1 (two T₁ R T₂)))) (splitSize s1 + splitSize s2)
    ≡⟨ refl ⟩ 
  sum _T+_ (sum _T*_ (ttgen T₁)) (splitSize s1 + splitSize s2)
    ≡⟨ {!!} ⟩ -- the last s2 are 0
  sum _T+_ (sum _T*_ (ttgen T₁)) (splitSize s1) ≡∎

-- same as tri1-T-...
tri2-T-sum-pow-commute : ∀ {s1 s2} -> (T : Tri (deeper s1 s2)) -> tri2 (T-sum-pow T) ≡ T-sum-pow (tri2 T)
tri2-T-sum-pow-commute = {!!}



-- or maybe define trt-mul?
rec-T-sum-pow-kind-of-commute : {s1 s2 : Splitting} {T : Tri (deeper s1 s2)} -> rec {s1} {s2} (sum _T+_ (sum _T*_ (ttgen T)) (splitSize s1 + splitSize s2)) ≡ 
                                                                                                                (sum _T+_ (sum _T*_ (ttgen (tri1 T))) (splitSize s1)) TS* ((rec T) ST* (sum _T+_ (sum _T*_ (ttgen (tri2 T))) (splitSize s2)))
rec-T-sum-pow-kind-of-commute {s1} {s2} {T} = {!!}


-- generate all

-- define transitive closure to be a relation between tri and tri. 


valiant-der' : ∀ {s1 s2  : Splitting} -> ∃ (λ f → min ≤T ₁∘ (Tis-a-transitive-closure-of {deeper s1 s2}) ⊒ fun f )
valiant-der' {s1} {s2} = ({!!} , 
  (⊒-begin
    min ≤T ₁∘ (Tis-a-transitive-closure-of {deeper s1 s2})
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
                            (sum _T+_ (sum _T*_ (ttgen a')) (splitSize s1 + splitSize s2)))
                           (rec
                            (sum _T+_ (sum _T*_ (ttgen a')) (splitSize s1 + splitSize s2)))
                           (tri2
                            (sum _T+_ (sum _T*_ (ttgen a')) (splitSize s1 + splitSize s2)))
                         ≡⟨ cong₂ (λ x' y' → two x' (rec
                                                   (sum _T+_ (sum _T*_ (ttgen a')) (splitSize s1 + splitSize s2))) y') (tri1-T-sum-pow-commute a') (tri2-T-sum-pow-commute a') ⟩
                         two 
                           (sum _T+_ (sum _T*_ (ttgen (tri1 a'))) (splitSize s1))
                           (rec
                            (sum _T+_ (sum _T*_ (ttgen a')) (splitSize s1 + splitSize s2)))
                           (sum _T+_ (sum _T*_ (ttgen (tri2 a'))) (splitSize s2))
                         ≡⟨ x ⟩
                         b ≡∎) ⟩
  fun (unsplit ∘ ⟨ T-sum-pow ∘ tri1 , rec ∘ T-sum-pow , T-sum-pow ∘ tri2 ⟩)
        ⊒⟨ (λ b a' z → z) ⟩
  fun (let A' = T-sum-pow ∘ tri1 
           B' = T-sum-pow ∘ tri2 in unsplit ∘ ⟨ A' , rec ∘ T-sum-pow  , B' ⟩)
        ⊒⟨ (λ b a' x → ≡-begin 
                       two (sum _T+_ (sum _T*_ (ttgen (tri1 a'))) (splitSize s1)) (rec (sum _T+_ (sum _T*_ (ttgen a')) (splitSize s1 + splitSize s2)))
                                                                                    (sum _T+_ (sum _T*_ (ttgen (tri2 a'))) (splitSize s2)) 
                       ≡⟨ cong (λ x' → two (sum _T+_ (sum _T*_ (ttgen (tri1 a'))) (splitSize s1)) x'
                                                                                                    (sum _T+_ (sum _T*_ (ttgen (tri2 a'))) (splitSize s2))) 
                          rec-T-sum-pow-kind-of-commute ⟩ 
                       two (sum _T+_ (sum _T*_ (ttgen (tri1 a'))) (splitSize s1)) ((sum _T+_ (sum _T*_ (ttgen (tri1 a'))) (splitSize s1)) TS* ((rec a') ST*
                           (sum _T+_ (sum _T*_ (ttgen (tri2 a'))) (splitSize s2))))
                         (sum _T+_ (sum _T*_ (ttgen (tri2 a'))) (splitSize s2))
                       ≡⟨ x ⟩ 
                       b ≡∎) ⟩
  fun (let A' = T-sum-pow ∘ tri1 
           B' = T-sum-pow ∘ tri2 in unsplit ∘ ⟨ A' , (λ x → (A' x) TS* ((rec x) ST* (B' x))) , B' ⟩) -- what about non-associativity???
        ⊒⟨ {!!} ⟩
  fun valiant
      ⊒∎))