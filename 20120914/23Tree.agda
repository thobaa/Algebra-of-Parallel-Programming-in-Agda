module 23Tree where

open import Data.Nat
open import Data.Product


data Carry (a : Set) : Set where
  one : a -> Carry a
  two : a -> a -> Carry a
    

data 23T (a : Set) : ℕ -> Set where
   empty : 23T a 0
   one   : (x : a) -> 23T a 0
   two  : ∀ {n} ->  (23T a n) ->  (23T a n) ->  23T a (1 + n)
   three  : ∀ {n} ->  (23T a n) ->  (23T a n) ->  (23T a n) -> 23T a (1 + n)

Tree = \a -> ∃ (23T a)


merge : ∀ {a n} -> Carry (23T a n) -> Tree a
merge (one x) = _ , x
merge (two x y) = _ , two x y

app2 : ∀ {a n} m -> 23T a (m + n) -> 23T a n -> Carry (23T a (m + n))
app2 zero t1 t2 = two t1 t2
app2 (suc m) ( (two _ y)) t2 with app2 m y t2
app2 (suc m) ( (two x₁ y)) t2 | one x₂ = one ( (two x₁ x₂))
app2 (suc m) ( (two x₁ y)) t2 | two x₂ x₃ = one ( (three  x₁ x₂ x₃))
app2 (suc m) ( (three _ _ y)) t2 with app2 m y t2 
app2 (suc m) ( (three x₁ x₂ y)) t2 | one x₃ = one ( (three x₁ x₂ x₃))
app2 (suc m) ( (three x₁ x₂ y)) t2 | two x₃ x₄ = two ( (two x₁ x₂)) ( (two x₃ x₄))

app2' : ∀ {a n} m -> 23T a n -> 23T a (m + n) -> Carry (23T a (m + n))
app2' = {!!}

data Ordering' : ℕ  → ℕ -> Set where
  less    : ∀ m k → Ordering' m (suc (k + m))
  equal   : ∀ m   → Ordering' m m
  greater : ∀ m k → Ordering' (suc (k + m)) m

compare' : ∀ m n → Ordering' m n
compare' m n = {!!}

app' : ∀ {a} -> Tree a -> Tree a -> ∃ \n -> Carry (23T a n)
app' (n1 , t1) (n2 , t2) with compare' n1 n2 
app' (n1 , t1) (.(suc (k + n1)) , t2) | less .n1 k = _ , (app2' (1 + k) t1 t2)
app' (.n2 , t1) (n2 , t2) | equal .n2 = _ , two t1 t2
app' (.(suc (k + n2)) , t1) (n2 , t2) | greater .n2 k = _ , app2 (1 + k) t1 t2



_++_ : ∀ {a} -> Tree a -> Tree a -> Tree a
x ++ y = merge (proj₂ (app' x y))


data Matrix {a : Set} : ∀ {n} -> 23T a n -> 23T a n -> Set where
  empty : ∀ {n t1 t2} → Matrix {a} {n} t1 t2 
  one : ∀ {x y} -> Matrix (one x) (one y)
  2x2 : ∀ {n x1 y1 x2 y2} -> Matrix {a} {n} x1 y1 -> Matrix x1 y2 -> Matrix x2 y1 -> Matrix x2 y2 -> Matrix (two x1 x2) (two y1 y2)
  -- TODO: 2x3 3x2 3x3

