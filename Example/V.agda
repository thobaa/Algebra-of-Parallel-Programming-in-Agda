module V where


open import Data.Nat
open import Cata
open import Function


open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality using (_≅_; ≅-to-≡)
open import Data.Nat.Properties
open import Algebra using (CommutativeSemiring)
open Algebra.CommutativeSemiring commutativeSemiring using (+-identity; +-comm; +-assoc)
open Relation.Binary.PropositionalEquality.≡-Reasoning



open import Data.Product

data Vec (a : Set) : ℕ -> Set where
  nilV  : Vec a 0
  consV : ∀ {n} -> a -> Vec a n -> Vec a (suc n)

congD : {n m : ℕ} -> (a : ℕ -> Set) -> n ≡ m -> a n ≡ a m 
congD a pf = cong a pf

--inspect : ∀ {a b} {A : Set a} {B : A → Set b}
--          (f : (x : A) → B x) (x : A) → Reveal (hide f x) is (f x)
--inspect f x = [ refl ]

cataVec : {a : Set} {b : ℕ ->  Set} {n m : ℕ} -> (nil' : b m ) -> (cons' : ∀ {o} -> a -> b o -> b (suc o)) -> Vec a n -> b (n + m)
cataVec {a} {b} {m = m} nil' cons' nilV = nil'
cataVec {a} {b} nil' cons' (consV y y') = cons' y (cataVec {a} {b} nil' cons' y')

data BinV (a : Set) : ℕ -> Set where
  tip : a -> BinV a 1
  bin : ∀ {n m} -> BinV a n -> BinV a m -> BinV a (n + m)

size : ∀ {a n} -> BinV a n -> ℕ
size {n = n} t = n


_++V_ : ∀ {a n m} -> Vec a n -> Vec a m -> Vec a (n + m)
nilV ++V b = b
consV y y' ++V b = consV y (y' ++V b)

-- doesn't seem to work with tip' : a -> b o, because it's added twice
cataBinV : {a : Set} {b : ℕ -> Set} {n : ℕ} -> 
           (tip' : a -> b 1) -> (bin' : ∀ {n' m'} -> b n' -> b m' -> b (n' + m')) 
           -> BinV a n -> b n
cataBinV tip' bin' (tip y) = tip' y
cataBinV {a} {b} tip' bin' (bin y y') with size y | size y' 
...| n | m = bin' {n} {m} (cataBinV {a} {b} tip' bin' y) (cataBinV {a} {b} tip' bin' y')

embedV : ∀ {a n} -> Vec a (suc n) -> BinV a (suc n)
embedV (consV y nilV) = tip y
embedV (consV y (consV y' y0)) = bin (tip y) (embedV (consV y' y0))

projV : ∀ {a n} -> BinV a n -> Vec a n
projV (tip y) = consV y nilV
projV (bin y y') = projV y ++V projV y'

theoremV : ∀ {a n} -> (v : Vec a (suc n)) -> projV (embedV v) ≡ v
theoremV (consV y nilV) = refl
theoremV (consV y (consV y' y0)) = cong (consV y) (theoremV (consV y' y0))

lemmaV : {a : Set} {b : ℕ -> Set} {n m z : ℕ} {k : b z } {f : ∀ {n'} -> a -> b n' -> b (suc n')} (x : Vec a n) (y : Vec a m) -> cataVec {a} {b} k f (x ++V y) ≡ cataVec {a} {b ∘ (λ x' → x' + z)} (cataVec {a} {b} k f y) f x
lemmaV nilV y = refl
lemmaV {a} {b} {f = f} (consV y y') y0 = cong (f y) (lemmaV {a} {b} y' y0)



Associative' : {A : ℕ -> Set} (f : ∀ {n' m'} -> A n' -> A m' -> A (n' + m')) -> Set
Associative' {A} f = ∀ {n m o} (x : A n) (y : A m) (z : A o) -> f {n + m} {o} (f {n} {m} x y) z ≅ f {n} {m + o} x (f {m} {o} y z)

lemmaV' : {a : Set} {b : ℕ -> Set} {n m : ℕ} {k : b 0} (i : a -> b 1) (_⊕_ : ∀{n' m'} -> b n' -> b m' -> b (n' + m')) -> Associative' {b} _⊕_ -> LeftUnit _⊕_ k -> (x : Vec a n) (y : Vec a m) -> cataVec {a} {b} {n + m} {0} k (_⊕_ ∘ i) (x ++V y) ≡ cataVec {a} {b} {n} {0} k (_⊕_ ∘ i) x ⊕ cataVec {a} {b} {m} {0} k (_⊕_ ∘ i) y
lemmaV' {k = k} i _⊕_ as lu nilV y = {!!} --sym (lu (cataVec k (_⊕_ ∘ i) y))
lemmaV' {k = k} i _⊕_ as lu (consV y y') y0 = {!!} {-begin
   i y ⊕ cataVec k (λ z → _⊕_ (i z)) (y' ++V y0) 
     ≡⟨ cong (_⊕_ (i y)) (lemmaV' i _⊕_ as lu y' y0) ⟩
   i y ⊕ (cataVec k (λ z → _⊕_ (i z)) y' ⊕ cataVec k (λ z → _⊕_ (i z)) y0)
     ≡⟨ sym (≅-to-≡  (as (i y) (cataVec k (λ z → _⊕_ (i z)) y')
                      (cataVec k (λ z → _⊕_ (i z)) y0))) ⟩
   (i y ⊕ cataVec k (λ z → _⊕_ (i z)) y') ⊕ cataVec k (λ z → _⊕_ (i z)) y0
     ∎-}



exerciseV' : {a b : Set} {n : ℕ} {empty' : b} {tip' : a -> b} {bin' : b -> b -> b} (x : BinV a n) -> Associative bin' -> Unit bin' empty' -> cataBinV tip' bin' x ≡ cataVec empty' (λ a b -> bin' (tip' a) b) (projV x)
exerciseV' {tip' = tip'} {bin' = bin'} (tip y) as unit = sym (proj₂ (unit (bin' (tip' y) (tip' y))) (tip' y))
exerciseV' {a} {b} {empty' = empty'} {tip' = tip'} {bin' = bin'} (bin y y') as un = begin 
  bin' (cataBinV tip' bin' y)
    (cataBinV tip' bin' y') ≡⟨ lemma'' {a} {b} {empty' = empty'} {tip'} {bin'} y y' as un ⟩ 
  bin' (cataVec empty' (λ z → bin' (tip' z)) (projV y))
    (cataVec empty' (λ z → bin' (tip' z)) (projV y'))
  ≡⟨ sym (lemmaV' tip' bin' as (λ ne → proj₁ (un ne) ne) (projV y)
            (projV y')) ⟩ 
  cataVec empty' (λ z → bin' (tip' z)) (projV y ++V projV y') ∎
  where
  lemma'' : {a b : Set} {n m : ℕ} {empty' : b} {tip' : a -> b} {bin' : b -> b -> b} -> (x : BinV a n) (y : BinV a m) -> Associative bin' -> Unit bin' empty' -> cataBinV tip' bin' (bin x y) ≡ bin' (cataVec empty' (λ a b -> bin' (tip' a) b) (projV x)) (cataVec empty' (λ a b -> bin' (tip' a) b) (projV y))
  lemma'' {bin' = bin'} x y as un = cong₂ bin' (exerciseV' x as un) (exerciseV' y as un)

exerciseV : {a b : Set} {n : ℕ} {empty' : b} {tip' : a -> b} {bin' : b ->  b -> b} (x y : BinV a n) -> 
  projV x ≡ projV y -> Associative bin' -> Unit bin' empty' -> cataBinV tip' bin' x ≡ cataBinV tip' bin' y
exerciseV {a} {b} {n} {empty'} {tip'} {bin'} x y pxpy ass pfunit = begin cataBinV tip' bin' x ≡⟨ exerciseV' {a} {b} {n} x ass pfunit ⟩ 
  cataVec empty' (λ z → bin' (tip' z)) (projV x) ≡⟨ cong (cataVec empty' (λ x' x0 → bin' (tip' x') x0)) pxpy ⟩ 
  cataVec empty' (λ z → bin' (tip' z)) (projV y) ≡⟨ sym (exerciseV' y ass pfunit) ⟩ 
  cataBinV tip' bin' y ∎

binVFusion : {a b c : Set} {n : ℕ} -> (h : b -> c) -> (x : BinV a n) -> {e : b} {s : a -> b} {_⊕_ : b -> b -> b} {_⊗_ : c -> c -> c} -> (∀ a b -> h (a ⊕ b) ≡ h a ⊗ h b) -> h (cataBinV s _⊕_ x) ≡ cataBinV (h ∘ s) _⊗_ x
binVFusion h (tip y) eq = refl
binVFusion h (bin y y') {e} {s} {_⊕_} {_⊗_} eq = begin 
  h (cataBinV s _⊕_ y ⊕ cataBinV s _⊕_ y') 
    ≡⟨ eq (cataBinV s _⊕_ y) (cataBinV s _⊕_ y') ⟩
  h (cataBinV s _⊕_ y) ⊗ h (cataBinV s _⊕_ y') 
    ≡⟨ cong₂ _⊗_ (binVFusion h y {e} eq) (binVFusion h y' {e} eq) ⟩
  cataBinV (λ z → h (s z)) _⊗_ y ⊗ cataBinV (λ z → h (s z)) _⊗_ y' ∎

mapBinV : ∀ {a b n} -> (a -> b) -> (BinV a n -> BinV b n)
mapBinV f (tip y) = tip (f y)
mapBinV f (bin y y') = bin (mapBinV f y) (mapBinV f y')

-- verkar som att man måste fixa en för 0 :(
binV-id : ∀ {a} {n : ℕ}  -> (id : a -> a) -> (identity id) -> (identity (mapBinV {a} {a} {n} id))
binV-id {a} {zero} id (Id pf) = {!!}
binV-id {a} {suc n} id (Id pf) = {!!} --Id helper
  where
  helper : (x : BinV a n) -> mapBinV id x ≡ x
  helper = {!!}
  --helper (tip y) = ?
  --helper (bin y y') = ?

-- input is a list of pairs, where first element is what it takes to go
-- to next thing, second to the thing after that ☺
input : Set -> ℕ -> Set
input a n = BinV (a × a) n

data Vtriang (a : Set) : ℕ -> Set where
  empty : Vtriang a 0
  one   : a -> Vtriang a 1

-- en lista med 

combine : ∀ {a n m} -> Vtriang a n -> Vtriang a m -> Vtriang a (n + m)
combine = {!!}

Valg : ∀ {a n} -> input a n -> Vtriang a n 
Valg {a} tree = {!!} -- cataBin {a × a} empty (λ x → one (proj₁ x)) {!combine!} tree --cataBin (Valg {!!}) {!!} {!!}

