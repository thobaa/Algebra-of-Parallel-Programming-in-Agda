module Matrix.Spec where

open import Matrix.Abstract
open import Data.Nat hiding (_⊓_)
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Binary
open import Data.Fin using (Fin; fromℕ; fromℕ≤; toℕ;  raise; reduce≥) 
                     renaming (zero to f0; suc to fsuc)

open import Level using () renaming (zero to Lzero)

-- AOPA
open import Relations
open import Relations.Minimum
open import Relations.Coreflexive
open import Sets

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

postulate 
  triangPf : ∀ {a} {da db m n p : ℕ} {A : Matrix a m n} {B : Matrix a n p} -> IsTriangular a da A -> IsTriangular a db B -> IsTriangular a (da + db) (Matrix* a A B)
 
-- is finite
sum-is-finite : {a : Set} -> (plus : a -> a -> a) -> (gen : ℕ -> a) -> Set
sum-is-finite plus gen = ∃ λ n → ∀ m → sum plus gen n ≡ sum plus gen (n + m)

-- for all n, transitive closure contains sum 1 to n M^k.
-- transitive closure least such.

-- example:
--∈ : {A : Set} → A ← ℙ A 
--∈ a s = s a 



-- need: relation on matrixes
-- for it, need relation on elements
postulate 
  ≤R : ∀ {R : Ring'} -> RC R ← RC R
  --_≤R_ : ∀ {R : Ring'} -> Rel (RC R) Lzero --(x : RC R) -> (y : RC R) -> Set 


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



-- min of "transitive closures", nej, är argumentet som ska vara triangulärt
valiant-der : ∀ {a n} -> ∃ λ f → fun f ⊑ valiant-spec {a} {n}
valiant-der = {!!}

-- idea: show that we get the finite sum below.
-- in it, introduce id before it, split id into putTogether∘takeApart
-- takeApart = (tri1, rect, tri2)  (takes matrix to respective part)
-- show that tri1, tri2 commutes with the sum.
-- show what happens with rect when moving it to other side.

-- transitive closure is sum
transclosure : ∀ {a n} -> (A : Matrix a n n) -> IsTriangular a 1 A -> Matrix a n n
transclosure {a} {n} A pf = sum (Matrix+ a) (matPow a A) n


