module Matrix.TwoThree where

open import Data.Nat
open import Data.Fin using (Fin; fromℕ; fromℕ≤; toℕ;  raise; reduce≥) 
                     renaming (zero to f0; suc to fsuc)
open import Data.Unit
open import Data.Empty


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

-- Branch = \a -> ∃ \ s -> Ix s -> a

data 23T : ℕ -> Set where
   empty : ∀ {n} -> 23T n
   one   : 23T 0
   deep  : ∀ {n} -> {s : Sz} -> (Ix s -> 23T n) -> 23T (1 + n)

data Mat (a : Set) : {n : ℕ} -> 23T n -> 23T n → Set where
  one : (x : a) -> Mat a one one
  zero : ∀ {n r c} -> Mat a {n} r c -- Note: for 2-3 trees this case can normally occur only at the top level.
  rec : ∀ {n} -> {sx sy : Sz} -> -- how this is divided
         {tx : Ix sx -> 23T n} -> {ty : Ix sy -> 23T n} -> -- subindices
          ((ix : Ix sx) -> (iy : Ix sy) -> Mat a (tx ix) (ty iy)) -> 
            Mat a (deep tx) (deep ty)


Sub : ∀ a {s n} -> Ix s -> Ix s -> (Ix s -> 23T n) -> Set

data Triangle (a : Set) : {n : ℕ} -> 23T n → Set where
  one : (x : a) -> Triangle a one 
  zero : ∀ {n s} -> Triangle a {n} s
  rec : ∀ {n} -> {s : Sz} -> -- how this is divided
            {t : Ix s -> 23T n} ->
             ((ix : Ix s) -> (iy : Ix s) -> Sub a ix iy t) -> 
               Triangle a (deep t)

Sub a left left t = Triangle a (t left)
Sub a left right t = Mat a (t left) (t right)
Sub a left mid t = Mat a (t left) (t mid)
Sub a right left t = ⊤
Sub a right right t = Triangle a (t right)
Sub a right mid t = ⊤
Sub a mid left t = ⊤
Sub a mid right t = Mat a (t mid) (t right)
Sub a mid mid t = Triangle a (t mid)

valiantOverlap : ∀ {n a} {s1 s2 : 23T n} -> Triangle a s1 -> Mat a s1 s2 -> Triangle a s2 -> Mat a s1 s2
valiantOverlap A (one x) C = one x
valiantOverlap A zero C = zero
valiantOverlap A (rec x) C = {!nested loop!!}



