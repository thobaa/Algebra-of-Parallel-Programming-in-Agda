module Matrix.TwoThree where

open import Data.Nat
open import Data.Fin using (Fin; fromℕ; fromℕ≤; toℕ;  raise; reduce≥) 
                     renaming (zero to f0; suc to fsuc)
open import Data.Unit
open import Data.Empty
open import Data.Product


data Sz : Set where
  two three : Sz

data Ix : Sz -> Set where
  left right : ∀ {a} -> Ix a
  mid : Ix three

_<=_ : ∀ {s} -> Ix s -> Ix s -> Set
left <= y = ⊤
mid <= left = ⊥
mid <= y = ⊤
right <= right = ⊤
right <= _ = ⊥

data 23T : ℕ -> Set where
   empty : 23T 0
   one   : 23T 0
   deep  : ∀ {n} -> (s : Sz) -> (Ix s -> 23T n) -> 23T (1 + n)

data Mat (a : Set) : {n : ℕ} -> 23T n -> 23T n → Set where
  one : (x : a) -> Mat a one one
  -- zero : ∀ {n r c} -> Mat a {n} r c -- Note: for 2-3 trees this case can normally occur only at the top level.
  rec : ∀ {n} -> {sx sy : Sz} -> -- how this is divided
         {tx : Ix sx -> 23T n} -> {ty : Ix sy -> 23T n} -> -- subindices
          ((ix : Ix sx) -> (iy : Ix sy) -> Mat a (tx ix) (ty iy)) -> 
            Mat a (deep sx tx) (deep sy ty)


Sub : ∀ a {s n} -> Ix s -> Ix s -> (Ix s -> 23T n) -> Set

data Triangle (a : Set) : {n : ℕ} -> 23T n → Set where
  one : (x : a) -> Triangle a one 
  -- zero : ∀ {n s} -> Triangle a {n} s
  rec : ∀ {n} -> {s : Sz} -> -- how this is divided
            {t : Ix s -> 23T n} ->
             ((ix : Ix s) -> (iy : Ix s) -> Sub a ix iy t) -> 
               Triangle a (deep s t)

Sub a left left t = Triangle a (t left)
Sub a left right t = Mat a (t left) (t right)
Sub a left mid t = Mat a (t left) (t mid)
Sub a right left t = ⊤
Sub a right right t = Triangle a (t right)
Sub a right mid t = ⊤
Sub a mid left t = ⊤
Sub a mid right t = Mat a (t mid) (t right)
Sub a mid mid t = Triangle a (t mid)

Branch = \(a : Set) (n : ℕ) -> ∃₂ \ (s : Sz) (t : Ix s -> 23T n) -> ((ix : Ix s) -> (iy : Ix s) -> Sub a ix iy t)

valiantOverlap : ∀ {n a} {s1 s2 : 23T n} -> Triangle a s1 -> Mat a s1 s2 -> Triangle a s2 -> Mat a s1 s2
valiantOverlap A (one x) C = one x
-- valiantOverlap A zero C = zero
valiantOverlap A (rec x) C = {!nested loop!!}


data Carry (a : Set) : Set where
  one : a -> Carry a
  two : a -> a -> Carry a

data CarryT (a : Set) n : Set where
  one : (s : 23T n) -> Triangle a s -> CarryT a n
  two : (s1 s2 : 23T n) -> Triangle a s1 -> Mat a s1 s2 -> Triangle a s2 -> CarryT a n
 

conc1 : ∀ {a n} -> Branch a n -> CarryT a n -> CarryT a (suc n)
conc1 (two , t , b) (one s x) = one (deep three {!!}) (rec {!!})
conc1 (two , t , b) (two s1 s2 x x₁ x₂) = {!!}
conc1 (three , t , b) (one s x) = {!!}
conc1 (three , t , b) (two s1 s2 x x₁ x₂) = {!!}

app2 : ∀ n m -> 23T (m + n) -> 23T n -> Carry (23T (m + n))
app2 = {!!} 

{-
app2 zero t1 t2 = two t1 t2
app2 (suc m) ( (two _ y)) t2 with app2 m y t2
app2 (suc m) ( (two x₁ y)) t2 | one x₂ = one ( (two x₁ x₂))
app2 (suc m) ( (two x₁ y)) t2 | two x₂ x₃ = one ( (three  x₁ x₂ x₃))
app2 (suc m) ( (three _ _ y)) t2 with app2 m y t2 
app2 (suc m) ( (three x₁ x₂ y)) t2 | one x₃ = one ( (three x₁ x₂ x₃))
app2 (suc m) ( (three x₁ x₂ y)) t2 | two x₃ x₄ = two ( (two x₁ x₂)) ( (two x₃ x₄))
-}

-- app2T : ∀ {a} n m  -> Triangle a s1 -> Triangle a s2 -> CarryT a 23T (m + n)
app2T = {!!}

