open import Definitions


open import Data.Vec
open import Data.Nat

open import Data.Product hiding (map)

open import Data.Fin as Fin using (Fin; zero; suc; toℕ; fromℕ)

open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; _≗_)
open import Relation.Binary.HeterogeneousEquality using (_≅_; refl)

module VecLemmas where

-- Lookup and map work together!
lookup-map : {n : ℕ} {A B : Set} -> (i : Fin n) -> (v : Vec A n) -> 
  (f : A -> B) -> lookup i (map f v) ≡ f (lookup i v) 
lookup-map {zero} () v f 
lookup-map {suc n} zero (v ∷ vs) f = refl
lookup-map {suc n} (suc i) (v ∷ vs) f = lookup-map {n} i vs f 


-- Row vectors containing all indices for a matrix.
rowIndices : (rs cs : ℕ) -> Vec (Vec ((Fin rs) × (Fin cs)) cs) rs
rowIndices rs cs = map (λ x → map (λ y → x , y) (allFin cs)) (allFin rs)

-- Not actually used:
--colIndices : (rs cs : ℕ) -> Vec (Vec ((Fin rs) × (Fin cs)) rs) cs
--colIndices rs cs = map (λ x → map (λ y → y , x) (allFin rs)) (allFin cs)


open import Relation.Binary.PropositionalEquality as P
  using (_≡_; _≢_) renaming (refl to eqrefl; sym to eqsym; cong to eqcong; cong₂ to eqcong₂) 

open import Data.Vec.Properties
open import Category.Applicative.Indexed
open P.≡-Reasoning
open Morphism
open import Function using (_$_; id)

-- Lemma for looking up elements in matrix. Pretty horrible stuff 
-- (but kind of fun to write).
lookRowInd : {m n : ℕ} -> (i : Fin m) -> (j : Fin n) -> 
  lookup j (lookup i (rowIndices m n)) ≡ (i , j)
lookRowInd {m} {n} i j = begin 
  lookup j
    (lookup i
     (replicate (λ x → replicate (_,_ x) ⊛ tabulate (λ x' → x')) ⊛
      tabulate (λ x → x))) 

  ≡⟨ eqcong (λ x → lookup j x) (op-⊛ (lookup-morphism i)
            (replicate (λ x → replicate (_,_ x) ⊛ tabulate (λ x' → x')))
            (tabulate (λ x → x))) ⟩

  lookup j
    (lookup i (replicate (λ x → replicate (_,_ x) ⊛ tabulate {n} (λ x' → x'))) $
    lookup i (tabulate {m} (λ x → x))) 

  ≡⟨ eqcong (λ x →
             lookup j
             (lookup i
             (replicate (λ x' → replicate (_,_ x') ⊛ tabulate {n} (λ x0 → x0)))
                  $ x)) (lookup∘tabulate (λ x → x) i) ⟩
  lookup j
    (lookup i (replicate (λ x → replicate (_,_ x) ⊛ tabulate {n} (λ x' → x'))) $
    i) 

  ≡⟨ eqcong (λ x → lookup j (x $ i)) (op-pure (lookup-morphism i) 
    (λ x → replicate (_,_ x) ⊛ tabulate {n} (λ x' → x'))) ⟩

  lookup j
    ((λ x → replicate (_,_ x) ⊛ tabulate {n} (λ x' → x')) $
    i)  

  ≡⟨ refl ⟩

  lookup j
    ((replicate (_,_ i) ⊛ tabulate {n} (λ x' → x')))  

  ≡⟨ op-⊛ (lookup-morphism j) (replicate (_,_ i)) (tabulate {n} (λ x' → x')) ⟩
  
  (lookup j (replicate (_,_ i)) $
  lookup j (tabulate {n} (λ x' → x'))) 

  ≡⟨ eqcong (λ x → lookup j (replicate (_,_ i)) $ x) (lookup∘tabulate (λ x → x)
                                                                      j) ⟩

  (lookup j (replicate (_,_ i)) $
  j)

  ≡⟨ eqcong (λ x -> x $ j) (op-pure (lookup-morphism j) (_,_ i)) ⟩

  (i , j) ∎