module PresentationC where

data ℕ : Set where
  zero  : ℕ
  suc   : ℕ → ℕ
{-
_+_ : ℕ → ℕ → ℕ
zero   + n = n
suc m  + n = suc (m + n)
-}
data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n} → zero ≤ n
  s≤s : ∀ {m n} → m ≤ n → suc m ≤ suc n

postulate R : Set

data Split : Set where
  one : Split
  bin : Split → Split → Split

data Vec : Split → Set where
  one : R → Vec one
  two : {a b : Split} → Vec a → Vec b → Vec (bin a b)
data Mat : Split → Split → Set where
  sing : R → Mat one one
--  rVec : {a b : Split} → Vec (bin a b) → Mat one (bin a b)
--  cVec : {a b : Split} → Vec (bin a b) → Mat (bin a b) one
  quad : ∀ {r₁ r₂ c₁ c₂}  → Mat r₁ c₁ → Mat r₁ c₂ 
                          → Mat r₂ c₁ → Mat r₂ c₂ 
                          → Mat (bin r₁ r₂) (bin c₁ c₂)

data Tri : Split → Set where
  one  : Tri one
  tri  : ∀ {a b} → Tri a  → Mat a b
                             → Tri b 
                             → Tri (bin a b)

postulate _T*_ : ∀ {s} → Tri s → Tri s → Tri s
          _T+_ : ∀ {s} → Tri s → Tri s → Tri s
          _R*_ : R → R → R
          _R+_ : R → R → R
          _TM*_ : ∀ {s t} → Tri s → Mat s t → Mat s t
          _MT*_ : R → R → R
          _≈_ : ∀ {s} → Tri s → Tri s → Set
infix 6 _T+_
infixl 6 _+_

--infix 4 _≈_
infix 7 _T*_
infix 4 _≈_
infix 7 _*_

_+_ : ∀ {a b} → Mat a b → Mat a b → Mat a b
sing x        + sing x'           = sing (x R+ x')
quad A B C D  + quad A' B' C' D'  = quad 
       (A + A') (B + B') 
       (C + C') (D + D')

_*_ : ∀ {a b c} → Mat a b → Mat b c → Mat a c
sing x        * sing x'           = sing (x R* x')
quad A B C D  * quad A' B' C' D'  = quad 
       (A * A' + B * C') (A * B' + B * D') 
       (C * A' + D * C') (C * B' + D * D')
--one T* one = one
--tri U R L T* tri U' R' L' = tri (U T* U') {!U TR* R' T+ R RT* L'!} (L T* L')

overlap : ∀ {a b} → Tri a → Mat a b → Tri b → Mat a b
overlap one (sing x) one = sing x
overlap (tri U₁ˣ R₁ˣ L₁ˣ) (quad A B C D) (tri U₂ˣ R₂ˣ L₂ˣ) = quad Aˣ Bˣ Cˣ Dˣ
  where Cˣ = overlap L₁ˣ C U₂ˣ
        Aˣ = overlap U₁ˣ (A + R₁ˣ * Cˣ) U₂ˣ
        Dˣ = overlap L₁ˣ (D + Cˣ * R₂ˣ) L₂ˣ
        Bˣ = overlap U₁ˣ (B + R₁ˣ * Dˣ + Aˣ * R₂ˣ) L₂ˣ

v : ∀ {s} → Tri s → Tri s
v one = one
v (tri U R L) = tri U⁺ (overlap U⁺ R L⁺) L⁺
  where U⁺ = v U
        L⁺ = v L

_is-tc-of_ : {s : Split} → Tri s → Tri s → Set
Cˣ is-tc-of C = Cˣ ≈ Cˣ T* Cˣ T+ C

v-correct : ∀ {s} {C : Tri s} → v C is-tc-of C
v-correct {one} {one} = {!!}
v-correct {(bin a b)} {tri U R L} = {!!}

is-otc-of : ∀ {a b} → Mat a b → Tri a → Mat a b → Tri b → Set
is-otc-of Rˣ U R L = {!Rˣ M≈ U T* Rˣ + !}

o-corr : ∀ {a b} → Tri a → Mat a b → Tri b → {!!}
o-corr Uˣ R Lˣ = {!!}