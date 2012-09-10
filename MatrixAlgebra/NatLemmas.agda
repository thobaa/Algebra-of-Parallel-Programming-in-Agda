open import Definitions


open import Data.Nat renaming (_⊔_ to max; _≤_ to _n≤_; _<_ to _n<_) 
open import Data.Nat.Properties

open import Algebra
open import Algebra.FunctionProperties
open import Relation.Binary
open import Relation.Binary.PropositionalEquality renaming (refl to eqrefl)
open ≡-Reasoning
open ≤-Reasoning renaming (begin_ to start_ ; _∎ to _□; _≡⟨_⟩_ to _≡⟨_⟩'_)
module NatLemmas where

open CommutativeSemiring commutativeSemiring renaming (_+_ to _n+_; zero to nzero)
open DecTotalOrder decTotalOrder


maxIsOne : {d1 d2 : ℕ} -> Either (max d1 d2 ≡ d1) (max d1 d2 ≡ d2)
maxIsOne {zero} {d2} = right eqrefl
maxIsOne {suc n} {zero} = left  eqrefl
maxIsOne {suc n} {suc m} with maxIsOne {n} {m}
... | (left pf) = left ( begin 
  suc (max n m)          ≡⟨ cong suc pf ⟩ 
  suc n ∎ )
... | (right pf) = right (begin suc (max n m) ≡⟨ cong suc pf ⟩ (suc m ∎))


-- If a + b < c, then either a < c or b < c
a+b<+=>a<c||b<c : {a b c : ℕ} -> a n+ b n< c -> Either (a n< c) (b n< c)
a+b<+=>a<c||b<c {zero}  {b} {c} pf = right pf
a+b<+=>a<c||b<c {suc n} {b} {c} pf = left (start
  suc (suc n)           ≤⟨ s≤s (s≤s (m≤m+n n b)) ⟩
  suc (suc (n + b))     ≤⟨ pf ⟩ 
  c □ )


-- Useful functions:
m≤m : {x : ℕ} -> x ≤ x
m≤m {zero} = z≤n
m≤m {suc n} = s≤s (m≤m {n})

m≤sm : {m : ℕ} -> m ≤ suc m
m≤sm {zero} = z≤n
m≤sm {suc m'} = s≤s m≤sm

-- Oposite of s≤s
p≤p : {a b : ℕ} -> suc a ≤ suc b -> a ≤ b
p≤p {zero} {b} pf = z≤n
p≤p {suc a} {zero} (s≤s ())
p≤p {suc a} {suc b} (s≤s pf) = pf