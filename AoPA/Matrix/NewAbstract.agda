-- Put new abstract stuff here before it typechecks!


open import Data.Nat
open import Data.Nat.Properties
open import Data.Fin using (Fin; fromℕ; fromℕ≤; toℕ;  raise; reduce≥; inject₁; inject+) 
                     renaming (zero to f0; suc to fsuc)

open import Data.Integer using (ℤ; +_; _-_)
                        -- renaming (≥ to z≥)
open import Matrix.Definitions using (toℤ) renaming (_≥_ to _z≥_; _<_ to _z<_)
open import Data.Empty
open import Matrix.ZLemmas
open import Matrix.NatLemmas
open import Algebra
open import Algebra.Structures
open import Data.Product
open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Function
open import Relation.Nullary.Core
open import Level             using () 
                              renaming (zero to zeroL)

open import Data.Vec renaming (zip to zipv; map to mapv)

open CommutativeSemiring commutativeSemiring using (+-identity; +-comm)

-- my stuff
open import Matrix.NonAssociativeRing as NAR

module NewAbstract (NAR : NonAssociativeRing zeroL zeroL) where

import Matrix.Abstract
open Matrix.Abstract (NAR)


-- sum of a_i from 0 to n
⨁ : {a : Set} → (plus : a → a → a) → (n : ℕ) → (aᵢ : Fin (suc n) → a) → a
⨁ _⊕_ zero aᵢ    = aᵢ f0
⨁ _⊕_ (suc n) aᵢ = ⨁ _⊕_ n (λ i → aᵢ (inject₁ i)) ⊕ aᵢ (fromℕ (suc n))

-- A^[k] = ∑₁ A^[i]*A[k-i], A^[1] = A

-- vector of all numbers summing to n
-- zip 0,1,...,n-1; n-1,...,0,1

--uncurry : ∀ {a b c} {A : Set a} {B : A → Set b} {C : Σ A B → Set c} →
--          ((x : A) → (y : B x) → C (x , y)) →
--          ((p : Σ A B) → C p)
--uncurry f (x , y) = f x y
--zip : ∀ {a b n} {A : Set a} {B : Set b} →
--      Vec A n → Vec B n → Vec (A × B) n
--zip = zipWith _,_
subVec : (n : ℕ) → Vec (Fin n × Fin n) n
subVec = uncurry′ zipv ∘ < id , reverse > ∘ allFin

{-subVec : (n : ℕ) → Vec (Fin n × Fin n) n
subVec zero = []
subVec (suc n) = (f0 , {!from!}) ∷ increaseFirst (subVec n)
  where 
    increaseFirst : Vec (Fin n × Fin n) n → Vec (Fin (suc n) × Fin (suc n)) n
    increaseFirst = {!!}
-}



--foldr : ∀ {a b} {A : Set a} (B : ℕ → Set b) {m} →
--        (∀ {n} → A → B n → B (suc n)) →
--        B zero →
--        Vec A m → B m
--foldr b _⊕_ n []       = n
--foldr b _⊕_ n (x ∷ xs) = x ⊕ foldr b _⊕_ n xs


-- 1 + 0 = 1, 1 + suc n = 2 + n, vill ha allt som summerar till 1 + n,
-- 1 , n   ; 2 , n-1 ; 3 , n-2 ;;; n   , 1 -- blir detta alla parenteser? 
-- 0 , n-1 ; 1 , n-2 ; 2 , n-3 ;;; n-1 , 0

-- raise m "n" = "m + n".

-- raise : ∀ {m} n → Fin m → Fin (n N+ m)
-- raise zero    i = i
-- raise (suc n) i = suc (raise n i)

-- raise' "m" n = "m + n"

raise' : ∀ {m} -> Fin m -> (n : ℕ) -> Fin (m + n)
raise' {m} i zero = subst Fin (sym (proj₂ +-identity m)) i
raise' {m} i (suc n) = subst Fin (begin suc (m + n) 
                                        ≡⟨ cong suc (+-comm m n) ⟩
                                        suc n + m
                                        ≡⟨ +-comm (suc n) m ⟩
                                        m + suc n ∎) (fsuc (raise' i n)) 

split : {i j k l : ℕ} -> Matrix (i + j) (k + l) -> 
                                  (Matrix i k × Matrix i l × 
                                   Matrix j k × Matrix j l )
split {i}{j}{k}{l} A = (λ i' j' → A (inject+ j i') (inject+ l j')) , (λ i' j' → A (raise' i' j) (raise k j')) , 
          (λ i' j' → A (raise i i') (raise' j' l)) , (λ i' j' → A (raise i i') (raise k j'))

unsplit : ∀ {i j k l} → (Matrix i k × Matrix i l × 
                         Matrix j k × Matrix j l ) → Matrix (i + j) (k + l)
unsplit {i}{j}{k}{l}
        (A , B , 
         C , D) i' k' with suc (toℕ i') ≤? i | suc (toℕ k') ≤? k 
unsplit (A , B , C , D) i' k'  | yes p | yes p' = A (reduce≤ i' p) (reduce≤ k' p')
unsplit (A , B , C , D) i' k'  | yes p | no ¬p  = B (reduce≤ i' p) (reduce≥ k' (p≤p (≰to> ¬p)))
unsplit (A , B , C , D) i' k'  | no ¬p | yes p  = C (reduce≥ i' (p≤p (≰to> ¬p))) (reduce≤ k' p)
unsplit (A , B , C , D) i' k'  | no ¬p | no ¬p' = D (reduce≥ i' (p≤p (≰to> ¬p))) (reduce≥ k' (p≤p (≰to> ¬p')))

split∘unsplit≡id : ∀ {i j k l rᵢ cᵢ} {A : Matrix (i + j) (k + l)} -> unsplit (split {i} {j} {k} {l} A) rᵢ cᵢ ≡ A rᵢ cᵢ
split∘unsplit≡id = {!!} 

-- define trisplit, and valiant


triSplit : ∀ {k l} → Triangle (k + l) → (Triangle k × Matrix k l × Triangle l)
triSplit (A , triangPf) = {!!} , {!!} , {!!} 
