module Matrix.STree where

open import Level using (Level)
open import Data.Product using (_×_; _,_)

data Splitting : Set where
  one : Splitting
  deeper  : Splitting -> Splitting -> Splitting


data STree (A : Set) : Splitting → Set where
  null  : STree A one
  fork : ∀ {s₁ s₂} → (x : A) → (T₁ : STree A s₁) → (T₂ : STree A s₂) → STree A (deeper s₁ s₂)


folds : {b : Level} {A : Set} {B : Splitting → Set b} {s : Splitting} → (fork' : ∀ {s₁ s₂} → (A × B s₁ × B s₂) → B (deeper s₁ s₂)) → (null' : B one) → STree A s → B s
folds fork' null' null = null'
folds {B = B} fork' null' (fork x T₁ T₂) = fork' (x , folds {B = B} fork' null' T₁ , folds {B = B} fork' null' T₂)


-- catamorphism:
-- h ∘ in = g (Fh) ≡ h = folds g

-- h (inF x) = g (Fh x)

-- där in : zero▿suc

-- null ▿ fork
-- inS = null ▿ fork : F μF → μF

-- om g från F a → a
-- så h från μF → a
-- h : Tri s → Tri s
-- F h : F (Tri s) → F (Tri s)
-- in : F (Tri s) → Tri s
-- => 
-- g : F (Tri s) → Tri s
-- vill hitta g som uppfyller h ∘ in = g (Fh)
-- där h = Tri-sum-pow!

-- för då är h = foldr g
-- sätt g = [one,?]

-- Träd.
-- F (Tree A) = 




-- h : STree A → STree A
-- in : F (STree A) → STree A

-- vad är F h?