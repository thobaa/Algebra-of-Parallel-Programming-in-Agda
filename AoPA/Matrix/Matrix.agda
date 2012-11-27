-- own files
--open import Definitions using ()
open import Matrix.VecLemmas    using (rowIndices; lookRowInd; lookup-map)


-- standard library:
open import Algebra      using (Ring)
open import Data.Product using (uncurry′; proj₁; proj₂; _,_)
open import Data.Sum     using (_⊎_) 
                         renaming (inj₁ to inj1; inj₂ to inj2)
open import Level        using () 
                         renaming (zero to zeroL)
open import Data.Vec     using (Vec; map; lookup; _++_; head; tail; foldl₁; 
                                _∷_; [])
open import Data.Nat     using (ℕ) 
                         renaming (_+_ to _n+_; zero to nzero; suc to nsuc)
open import Data.Nat.Properties using (n∸m≤n)
open import Data.Fin     using (Fin; _ℕ-_; inject≤; inject₁; toℕ; fromℕ) 
                         renaming (zero to fzero; suc to fsuc; pred to fpred)
open import Data.Bool    using (Bool; _∧_; _∨_; true; false)
open import Function     using (flip; _$_)
open import Algebra.Props.Ring  using ()

import Relation.Binary.EqReasoning as EqR 
            using () 
            renaming (begin_ to Rbegin_; _≈⟨_⟩_ to _R≈⟨_⟩_; _∎ to _R∎ )
open import Relation.Binary.PropositionalEquality as P 
            using (_≡_; refl; sym; cong)

module Matrix 
  (A : Ring zeroL zeroL) -- is this ok??? 
where

open P.≡-Reasoning using (begin_; _∎; _≡⟨_⟩_)

open Algebra.Ring A using (setoid; 0#; _*_; _+_; _≈_; *-cong; zero; +-cong; 
                           +-identity; 1#) 
                    renaming (refl to Rrefl; trans to Rtrans)

open EqR setoid using (Rbegin_; _R≈⟨_⟩_; _R∎) -- no idea what this means, from ring properties file.

-- short name for set with ring elements
R : Set
R = Ring.Carrier A

-- Datatype for ring-matrix (in the future, simply "Matrix").
-- Matrix is just a function from indices to Ring, when transformed into
-- Vec (Vec R), rows are easier to work with, I think.
data Matrix (rs : ℕ) (cs : ℕ) : Set where
  fMatrix : (Fin rs -> Fin cs -> R) -> Matrix rs cs

Matrix' : ℕ -> ℕ -> Set
Matrix' rs cs = Fin rs -> Fin cs -> R

-- Datatype for "semantic matrix" (idea from the slides) not used much
data semMatrix (rs : ℕ) (cs : ℕ) {A : Set} : Set where
  sMatrix : (Fin rs -> Fin cs -> A) -> semMatrix rs cs

-- pred : ∀ {n} → Fin (nsuc n) → Fin n
-- pred (fsuc i) = i

Vec' : ℕ -> Set
Vec' n = Fin n -> R

{-
tail' : ∀ {n} -> Vec' (nsuc n) -> Vec' n
tail' f fzero = {!!}
tail' f (fsuc i) = {!!}
-}

scalar : {n : ℕ} -> Vec' n -> Vec' n -> R
scalar {nzero}  f g = 0#
scalar {nsuc n} f g = f fzero * g fzero  +  scalar (\x -> f (fsuc x)) 
                                                   (\x -> g (fsuc x))

-- C-c C-c for fill-in case skeleton
-- C-c C-a autofill using Agsy

matprod : ∀ {a b c} -> Matrix' a b -> Matrix' b c -> Matrix' a c
matprod {a}{b}{c} f g = \i j -> scalar {b} (λ z → f i z) (λ z → g z j)


----------------------------------------------
--Helpful programming functions
----------------------------------------------

-- Sematic matrix to matrix
toMatrix : {rs cs : ℕ} -> semMatrix rs cs {R} -> Matrix rs cs
toMatrix (sMatrix f) = fMatrix f

-- Matrix to semantic matrix
fromMatrix : {rs cs : ℕ} -> Matrix rs cs -> semMatrix rs cs {R}
fromMatrix (fMatrix f) = sMatrix f

-- Helper function for generating rows
rowMap : {rs cs : ℕ} {A : Set} -> (Fin rs -> Fin cs -> A) -> Vec (Vec A cs) rs
rowMap {rs} {cs} f = map (map (uncurry′ f)) (rowIndices rs cs)

-- Helper function for generating columns
colMap : {rs cs : ℕ} {A : Set} -> (Fin rs -> Fin cs -> A) -> Vec (Vec A rs) cs
colMap {rs} {cs} f = rowMap {cs} {rs} (flip f)

-- Extract vector of columns from semantic matrix
scols : {rs cs : ℕ} {A : Set} -> semMatrix rs cs {A} -> Vec (Vec A rs) cs 
scols {rs} {cs} (sMatrix f) = colMap f

-- Extract vector of rows from semantic matrix
srows : {rs cs : ℕ} {A : Set} -> semMatrix rs cs {A} -> Vec (Vec A cs) rs
srows {rs} {cs} (sMatrix f) = rowMap f 

-- Build semantic matrix from vector of columns
scolsToMatrix : {rs cs : ℕ} {A : Set} -> Vec (Vec A rs) cs -> semMatrix rs cs
scolsToMatrix = λ x → sMatrix (λ x' x0 → lookup x' (lookup x0 x) )

-- Build semantic matrix from vector of columns
srowsToMatrix : {rs cs : ℕ} {A : Set} -> Vec (Vec A cs) rs -> semMatrix rs cs
srowsToMatrix = λ x → sMatrix (λ x' x0 → lookup x0 (lookup x' x))


-- Extract vector of rows from matrix
rows : {rs cs : ℕ} -> Matrix rs cs -> Vec (Vec R cs) rs
rows {rs} {cs} (fMatrix f) = rowMap f

-- Extract vector of columns from matrix
cols : {rs cs : ℕ} -> Matrix rs cs -> Vec (Vec R rs) cs
cols {rs} {cs} (fMatrix f) = colMap f

-- Build matrix from vector of columns
colsToMatrix : {rs cs : ℕ} -> Vec (Vec R rs) cs -> Matrix rs cs
colsToMatrix cs = toMatrix (scolsToMatrix cs)

-- Build matrix from vector of columns
rowsToMatrix : {rs cs : ℕ} -> Vec (Vec R cs) rs -> Matrix rs cs
rowsToMatrix rs = toMatrix (srowsToMatrix rs) 


-- Combine two Matrixes (not used yet, could generalize to semantic matrixes)
-- by concatenating them
_<>_     : {n m p : ℕ} ->  Matrix n m -> Matrix n p -> Matrix n (m n+ p)
A <> B = colsToMatrix (cols A ++ cols B)

-- Combine two Matrixes (not used yet, could generalize to semantic matrixes)
-- by putting first matrix over second matrix
_over_     : {n m p : ℕ} ->  Matrix m p -> Matrix n p -> Matrix (m n+ n) p 
A over B = rowsToMatrix (rows A ++ rows B)



----------------------------------------------
--"Algebraic" functions
----------------------------------------------


-- Dot product between two vectors with elements in Ring (also helper function
-- for matrix multiplication!
<_,_> : {n : ℕ} -> Vec R n -> Vec R n -> R
<_,_> {nzero} v1 v2 = 0#
<_,_> {nsuc _} v1 v2 = head v1 * head v2 + < (tail v1) , (tail v2) >

-- Helper function for matrix multiplication (the (i,j)th element in the new
-- matrix) (partly because it makes pattern matching easier)
matfun : {m n p : ℕ} -> Matrix m n -> Matrix n p -> (Fin m -> Fin p -> R)
matfun A B i j = < lookup i (rows A) , lookup j (cols B) >

-- Matrix multiplication!
infixl 7 _m*_ 
_m*_ : {m n p : ℕ} -> Matrix m n -> Matrix n p -> Matrix m p
A m* B = fMatrix (matfun A B)


-- Lookup in semantic matrix
_!![_,_] : {n m : ℕ} {A : Set} -> semMatrix n m -> Fin n -> Fin m -> A
(sMatrix f) !![ i , j ] = f i j

-- Lookup in Matrix
_![_,_] : {n m : ℕ} -> Matrix n m -> Fin n -> Fin m -> R
(fMatrix f) ![ i , j ] = f i j







-- Apply function to all elements in semantic matrix
mMap : {n m : ℕ} {A B : Set} -> (A -> B) -> semMatrix (nsuc n) (nsuc m) {A}
                                         -> semMatrix (nsuc n) (nsuc m) {B}
mMap f (sMatrix g) = sMatrix (λ x y → f (g x y))

-- And of two semantic matrixes
mand : {n m : ℕ} -> semMatrix n m {Bool} -> semMatrix n m {Bool}
                 -> semMatrix n m {Bool}
mand (sMatrix f) (sMatrix g) = sMatrix (λ i j → f i j ∧ g i j) 

-- Or of two semantic matrixes
mor : {n m : ℕ} -> semMatrix n m {Bool} -> semMatrix n m {Bool}
                -> semMatrix n m {Bool}
mor (sMatrix f) (sMatrix g) = sMatrix (λ i j → f i j ∨ g i j) 

-- And of a semantic matrix (true iff every element is true)
mAnd : {n m : ℕ} -> semMatrix (nsuc n) (nsuc m) {Bool} -> Bool
mAnd A = foldl₁ _∧_ (map (λ x → foldl₁ _∧_ x) (scols A))

-- Or of a semantic matrix (true iff any element is true)
mOr : {n m : ℕ} -> semMatrix (nsuc n) (nsuc m) {Bool} -> Bool
mOr A = foldl₁ _∨_ (map (λ x → foldl₁ _∨_ x) (scols A))






-- Two vectors (v1, ..., vn) and (u1, ..., un) are orthogonal if for every 
-- 0 ≤ i ≤ n, ui = 0 or vi = 0
data simpleOrth {n : ℕ} (x y : Vec R (nsuc n)) : Set where
  sOrth : ((i : Fin (nsuc n)) -> (lookup i x ≈ 0#) ⊎ (lookup i y ≈ 0#)) ->
          simpleOrth x y 


-- Lemma for proving simpleOrth => Orthogonal
head≈lookup0 : {n : ℕ} -> (x : Vec R (nsuc n)) -> head x ≈ lookup fzero x
head≈lookup0 (a ∷ as) = Rrefl

-- Lemma for proving simpleOrth => Orthogonal
lookupInTail : {n : ℕ} {i : Fin n} -> (x : Vec R (nsuc n)) -> lookup i (tail x) ≈ lookup (fsuc i) x
lookupInTail (x ∷ xs) = Rrefl

-- Lemma for proving simpleOrth => Orthogonal
head0 : {n : ℕ} (x y : Vec R (nsuc n)) -> (lookup fzero x ≈ 0#) ⊎ 
                                          (lookup fzero y ≈ 0#) -> 
        head x * head y ≈ 0#

head0 x y (inj1 x0≈0) = Rbegin
  head x * head y                   R≈⟨ *-cong (head≈lookup0 x) Rrefl ⟩
  lookup fzero x * head y           R≈⟨ *-cong x0≈0 Rrefl ⟩
  0#     * head y                   R≈⟨ proj₁ zero _ ⟩
  0# R∎
head0 x y (inj2  y0≈0) = Rbegin
  head x * head y                   R≈⟨ *-cong Rrefl (head≈lookup0 y) ⟩
  head x * lookup fzero y           R≈⟨ *-cong Rrefl y0≈0 ⟩
  head x * 0#                       R≈⟨ proj₂ zero _ ⟩
  0# R∎

-- Helper function for proving simpleOrth => Orthogonal, translates lookup
-- function for removing head
newfun : {n : ℕ} {x y : Vec R (nsuc (nsuc n))} -> 
  ((i : Fin (nsuc (nsuc n))) -> (lookup i x ≈ 0#) ⊎ (lookup i y ≈ 0#)) -> 
  ((i : Fin (nsuc n)) -> (lookup i (tail x) ≈ 0#) ⊎ (lookup i (tail y) ≈ 0#))
newfun {_} {x} {y} f i with f (fsuc i)
...| inj1 x0≈0 = inj1 (Rtrans (lookupInTail x) x0≈0)
...| inj2 y0≈0 = inj2 (Rtrans (lookupInTail y) y0≈0)

-- Remove head of while keeping proof of orthogonality
removeHead : {n : ℕ} {x y : Vec R (nsuc (nsuc n))} -> simpleOrth x y 
             -> simpleOrth (tail x) (tail y)
removeHead {_} {x} {y} (sOrth pf) = sOrth $ newfun pf

-- SimpleOrth => Orthogonal (i. e., <_,_> == 0#)
simpleOrthOrth : {n : ℕ} {x y : Vec R (nsuc n)} -> simpleOrth x y -> 
                 < x , y > ≈ 0#
simpleOrthOrth {nzero} {x} {y} (sOrth pf) = Rbegin 
  head x * head y + 0#                   R≈⟨ +-cong (head0 x y (pf fzero)) Rrefl ⟩
  0# + 0#                                R≈⟨ proj₂ +-identity _ ⟩
  0# R∎
simpleOrthOrth {nsuc n} {x} {y} (sOrth pf) = Rbegin
  head x * head y + < tail x , tail y >  R≈⟨ +-cong (head0 x y (pf fzero)) Rrefl ⟩
  0# + < tail x , tail y >               R≈⟨ proj₁ +-identity _ ⟩
  < tail x , tail y >                    R≈⟨ simpleOrthOrth {n} {tail x} {tail y}
                                            (removeHead {_} {x} {y} (sOrth pf))⟩
  0# R∎


-- Lookup in matrix == Lookup in lookup in rows. Probably useful enough to get
-- a proper name!
lookupLemma1 : {m n : ℕ} (A : Matrix m n) -> (i : Fin m) -> (k : Fin n) -> (A ![ i , k ] ≡ lookup k (lookup i (rows A)))
lookupLemma1 {m} {n} (fMatrix f) i k = begin 
  f i k ≡⟨ refl ⟩
  uncurry′ f ( i , k )
              
  ≡⟨ cong (uncurry′ f) (sym (lookRowInd i k)) ⟩
  
  uncurry′ f (lookup k (lookup i (rowIndices m n)))
  
  ≡⟨ sym (lookup-map k (lookup i (rowIndices m n)) 
           (uncurry′ f)) ⟩
  
  lookup k (map (uncurry′ f) (lookup i (rowIndices m n))) 

  ≡⟨ cong (λ x → lookup k x) (sym (lookup-map i 
           (rowIndices m n) (map (λ y → uncurry′ f y)))) ⟩

  lookup k (lookup i (rows (fMatrix f))) ∎

-- Lookup in matrix == Lookup in lookup in cols.
lookupLemma2 : {m n : ℕ} (A : Matrix m n) -> (i : Fin m) -> (k : Fin n) -> (A ![ i , k ] ≡ lookup i (lookup k (cols A)))
lookupLemma2 {m} {n} (fMatrix f) i k = begin
  f i k ≡⟨ refl ⟩
  uncurry′ f ( i , k )
              
  ≡⟨ cong (uncurry′(flip f)) (sym (lookRowInd k i)) ⟩
  
  uncurry′ (flip f) (lookup i (lookup k (rowIndices n m)))
  
  ≡⟨ sym (lookup-map i (lookup k (rowIndices n m)) 
           (uncurry′ (flip f))) ⟩
  
  lookup i (map (uncurry′ (flip f)) (lookup k (rowIndices n m)))

  ≡⟨ cong (λ x → lookup i x) (sym (lookup-map k 
           (rowIndices n m) (map (λ y → uncurry′ (flip f) y)))) ⟩

  lookup i (lookup k (cols (fMatrix f))) ∎


-- examples
rb1 = true ∷ false ∷ true ∷ []
rb2 = false ∷ true ∷ true ∷ []
rb3 = true ∷ true ∷ true ∷ []

mb1 = srowsToMatrix (rb1 ∷ rb2 ∷ rb3 ∷ [])
mb2 = srowsToMatrix (rb3 ∷ [])

row1 : Vec R 3
row1 = 1# ∷ 1# ∷ 1# ∷ []
row2 : Vec R 3
row2 = 0# ∷ 1# ∷ 1# ∷ []
row3 : Vec R 3
row3 = 0# ∷ 0# ∷ 1# ∷ []

m1 : Matrix 3 3
m1 = rowsToMatrix (row1 ∷ row2 ∷ row3 ∷ [])
