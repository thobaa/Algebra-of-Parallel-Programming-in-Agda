open import Data.List
open import Data.Product
open import Data.Product.N-ary
open import Data.Bool
open import Data.Unit
open import Data.Nat
module Example where

-- grammar: 
-- S   -> NP VP
-- VP  -> VP PP
-- VP  -> V NP
-- VP  -> eats
-- PP  -> P NP
-- NP  -> Det N
-- NP  -> she
-- V   -> eats
-- P   -> with
-- N   -> fish
-- N   -> fork
-- Det -> a

-- nbr of elements: ∅, Det, N, P, V, NP, PP, VP, S

-- initial matrix: 
-- she | eats | a | fish | with | a | fork on the above diagonal: 

-- NP, V + VP, Det, N, P, Det, N 
 

-- example ring, elements in sets: (need to model addition)
{-data Car : Set where
  S   : Car
  VP  : Car
  PP  : Car
  NP  : Car
  V   : Car
  P   : Car
  N   : Car
  Det : Car-}
--  ∅   : Car

-- use product instead:
car : Set
car = Bool ^ 8

_+'_ : car → car → car
(x₁ , x₂ , x₃ , x₄ , x₅ , x₆ , x₇ , x₈) +' (y₁ , y₂ , y₃ , y₄ , y₅ , y₆ , y₇ , y₈) = (x₁ ∨ y₁ , x₂ ∨ y₂ , x₃ ∨ y₃ , x₄ ∨ y₄ , x₅ ∨ y₅ , x₆ ∨ y₆ , x₇ ∨ y₇ , x₈ ∨ y₈)


-- multiplicationstabell från ovan.
-- (S, VP, PP, NP, V, P, N, Det)
-- gör det coordinatvis på något sätt.
-- grammar: 
-- S   -> NP VP
-- VP  -> VP PP
-- VP  -> V NP
-- PP  -> P NP
-- NP  -> Det N
∅ : car
∅ = (false , false , false , false , false , false , false , false)

_*'_ : car → car → car
a *' b = (S a b , VP a b , PP a b , NP a b , V a b , P a b , N a b , Det a b)
  where S       : car → car → Bool
        S (s , vp , pp , np , xs) (s' , vp' , pp' , ys) = {!!}
        VP      : car → car → Bool
        VP a b  = {!!}
        PP      : car → car → Bool
        PP a b  = {!!}
        NP      : car → car → Bool
        NP a b  = {!!}
        V       : car → car → Bool
        V a b   = false
        P       : car → car → Bool
        P a b   = false
        N       : car → car → Bool
        N a b   = false
        Det     : car → car → Bool
        Det a b = false
{-

data _∈'_ : Car → List Car → Set where
  x∈x∷xs : ∀ {x xs} → x ∈' (x ∷ xs)
  ∈-cons  : ∀ {x y xs} → (x∈xs : x ∈' xs) → x ∈' (y ∷ xs)





data _∉_ : Car → List Car → Set where
  x∉[]    : ∀ {x} → x ∉ []
  x∉y∷ys : ∀ {x y ys} → x ∉ ys → x ≢ y → x ∉ (y ∷ ys)

-- a simple set: 
Sets₁ : Set
Sets₁ = Σ (List Car) noDoubles
  where noDoubles : List Car → Set
        noDoubles [] = ⊤
        noDoubles (S ∷ xs) = {!!}
        noDoubles (VP ∷ xs) = {!!}
        noDoubles (PP ∷ xs) = {!!}
        noDoubles (NP ∷ xs) = {!!}
        noDoubles (V ∷ xs) = {!!}
        noDoubles (P ∷ xs) = {!!}
        noDoubles (N ∷ xs) = {!!}
        noDoubles (Det ∷ xs) = {!!}



  -}