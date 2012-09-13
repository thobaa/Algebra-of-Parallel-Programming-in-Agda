-- own:
--open import Definitions using ()

-- standard library:
open import Data.Sum            using (_⊎_) 
                                renaming (inj₁ to inj1; inj₂ to inj2)
open import Data.Nat            using (decTotalOrder; ℕ; suc; zero; s≤s; _+_; 
                                       z≤n) 
                                renaming (_⊔_ to max; _≤_ to _n≤_; _<_ to _n<_)
open import Data.Nat.Properties using (commutativeSemiring; m≤m+n)
open import Algebra             using (CommutativeSemiring)
--open import Algebra.FunctionProperties using ()
open import Relation.Binary     using ()
open Data.Nat.≤-Reasoning       using (_≤⟨_⟩_) 
                                renaming (begin_ to ≤begin_ ; _∎ to _≤∎)
open import Relation.Binary.PropositionalEquality      using (_≡_; cong) 
                                                       renaming (refl to eqrefl)
open Relation.Binary.PropositionalEquality.≡-Reasoning using (begin_; _≡⟨_⟩_;_∎)
open Algebra.CommutativeSemiring commutativeSemiring   using () 
                                                       renaming (_+_ to _n+_; 
                                                                 zero to nzero)
open Relation.Binary.DecTotalOrder decTotalOrder       using (_≤_)

module NatLemmas where

maxIsOne : {d1 d2 : ℕ} -> (max d1 d2 ≡ d1) ⊎ (max d1 d2 ≡ d2)
maxIsOne {zero} {d2} = inj2 eqrefl
maxIsOne {suc n} {zero} = inj1  eqrefl
maxIsOne {suc n} {suc m} with maxIsOne {n} {m}
... | (inj1 pf) = inj1 ( begin 
  suc (max n m)          ≡⟨ cong suc pf ⟩ 
  suc n ∎ )
... | (inj2 pf) = inj2 (begin suc (max n m) ≡⟨ cong suc pf ⟩ (suc m ∎))


-- If a + b < c, then either a < c or b < c
a+b<+=>a<c||b<c : {a b c : ℕ} -> a n+ b n< c -> (a n< c) ⊎ (b n< c)
a+b<+=>a<c||b<c {zero}  {b} {c} pf = inj2 pf
a+b<+=>a<c||b<c {suc n} {b} {c} pf = inj1 (≤begin
  suc (suc n)           ≤⟨ s≤s (s≤s (m≤m+n n b)) ⟩
  suc (suc (n + b))     ≤⟨ pf ⟩ 
  c ≤∎)


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