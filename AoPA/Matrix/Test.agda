open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Product
open import Data.Nat
open import Data.Sum
open import Function
open import Data.Unit

import Matrix.Abstract

import Matrix.NewNewSplit
open import Matrix.STree

open import Matrix.NonAssociativeRing

open import Level using () renaming (zero to Lzero)



module Matrix.Test (NAR : NonAssociativeRing Lzero Lzero) where

open Matrix.Abstract (NAR)
open Matrix.NewNewSplit (NAR)

-- should be defined for all

-- defining uncurried (curried?) stuff for help
data SplittingC : Set where
  one : SplittingC
  deeper : (SplittingC × SplittingC) → SplittingC
data VecC : SplittingC → Set where
  one : R → VecC one
  two : ∀ {s1 s2} → VecC s1 → VecC s2 → VecC (deeper (s1 , s2))
data MatC : (SplittingC × SplittingC) → Set where
  Sing : (x : R) -> MatC (one , one)
  RVec : ∀{s₁ s₂} -> VecC (deeper (s₁ , s₂)) -> MatC (one , (deeper (s₁ , s₂)))
  CVec : ∀{s₁ s₂} -> VecC (deeper (s₁ , s₂)) -> MatC ((deeper (s₁ , s₂)) , one)
  quad : ∀{r1 r2 c1 c2} -> MatC (r1 , c1) -> MatC (r1 , c2) -> 
                           MatC (r2 , c1) -> MatC (r2 , c2) -> 
                           MatC ((deeper (r1 , r2)) , (deeper (c1 , c2)))
data TriC : SplittingC → Set where
  one : TriC one
  two : ∀ {s1 s2} → (TriC s1 × MatC (s1 , s2) × 
                               TriC s2) →
                     TriC (deeper (s1 , s2))

-- + of functions
《_》T : ∀ {s} {a : SplittingC → Set} → (a one) × (∀ {s1 s2} → a s1 × MatC (s1 , s2) × a s2 → a (deeper (s1 , s2))) → TriC s → a s
《 one' , two' 》T one = one'
《 one' , two' 》T  (two (t1 , r , t2)) = two' (《 one' , two' 》T t1 , r , 《 one' , two' 》T t2)
 
data ListC (A : Set) : Set where
  nil  : ⊤ → ListC A
  cons : (A × ListC A) → ListC A

《_》L : ∀ {A} {b : Set} → ((⊤ → b) × (A × b → b)) →  ListC A → b
《 nil' , cons' 》L (nil ⊤) = nil' ⊤
《 nil' , cons' 》L (cons (x , xs)) = cons' (x , 《 nil' , cons' 》L xs)

thm : {A : Set} {xs : ListC A} → 《 nil , cons 》L xs ≡ xs
thm {A} {nil ⊤} = refl
thm {A} {cons (x , xs)} = cong (λ xs' → cons (x , xs')) thm

sum : ListC ℕ → ℕ
sum = 《 (λ _ → 0) , (uncurry _+_) 》L 

vo : ∀ {s1 s2} → TriC (deeper (s1 , s2)) → MatC (s1 , s2)
vo = {!!}

-- valiant-sum-n
-- 

-- X should be fixed point of 
-- X (two (two (A₁ , A₂ , A₃) , quad (C₂ , C₄ , C₁ , C₃) , two (B₃ , B₂ , B₁)))
--  = 
--   quad ( X (two (A₁ , C₂ M+  , B₃ ) , 

-- eller 
-- X (two (A₁ , A₂ , A₃) , quad (C₂ , C₄ , C₁ , C₃) , two (B₃ , B₂ , B₁))
-- = 
-- quad ( X (A₁ , C₂ M+ (A₂ M* ?) , B₃) , X (A₁ , ? , B₁) , 
--        X (A₃ , C₁ , B₃) , X ( A₃ , C₃ M+ (? M* B₂) , B₁) )

-- X (two (t1, RVec, t2)) =  quad (   ,   ,   ,   )
--
--
--
--                        if one if RVec if CVec if quad
-- i. e., four functions [      ,       ,       ,       ]
