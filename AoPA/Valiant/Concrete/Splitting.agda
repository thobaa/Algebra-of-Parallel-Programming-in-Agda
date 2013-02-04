open import Data.Nat using (ℕ; _+_; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Fin using (Fin) 
                     renaming (zero to f0; suc to fsuc)

module Valiant.Concrete.Splitting where

data Splitting : Set where
  one : Splitting
  deeper  : Splitting -> Splitting -> Splitting


splitSize : Splitting → ℕ
splitSize one = 1 
splitSize (deeper s1 s2) = splitSize s1 + splitSize s2


simpleSplit : ℕ → Splitting
simpleSplit zero = one
simpleSplit (suc n) = deeper one (simpleSplit n)

injFin : ∀ {n} → Fin (splitSize (simpleSplit n)) → Fin (suc n) 
injFin {zero} f0 = f0
injFin {zero} (fsuc i) = fsuc i
injFin {suc n} f0 = f0
injFin {suc n} (fsuc i) = fsuc (injFin {n} i)

outFin : ∀ {n} → Fin (suc n) → Fin (splitSize (simpleSplit n))
outFin {zero} f0 = f0
outFin {zero} (fsuc ())
outFin {suc n} f0 = f0
outFin {suc n} (fsuc i) = fsuc (outFin {n} i)




-- PROOFS
splitSize∘simpleSplit≡suc : (n : ℕ) → splitSize (simpleSplit n) ≡ suc n 
splitSize∘simpleSplit≡suc zero = refl
splitSize∘simpleSplit≡suc (suc n) = cong suc (splitSize∘simpleSplit≡suc n)




injFin∘outFin≡id : ∀ {n i} → injFin (outFin {n} i) ≡ i
injFin∘outFin≡id {zero} {f0} = refl
injFin∘outFin≡id {zero} {fsuc ()}
injFin∘outFin≡id {suc n} {f0} = refl
injFin∘outFin≡id {suc n} {fsuc i} = cong fsuc injFin∘outFin≡id

outFin∘injFin≡id : ∀ {n i} → outFin (injFin {n} i) ≡ i
outFin∘injFin≡id {zero} {f0} = refl
outFin∘injFin≡id {zero} {fsuc ()}
outFin∘injFin≡id {suc n} {f0} = refl
outFin∘injFin≡id {suc n} {fsuc i} = cong fsuc (outFin∘injFin≡id {n})
