import Matrix.Abstract
import Matrix.Tri
import Matrix.TriFold
import Matrix.NewNewSplit
open import Matrix.STree
open import Data.Nat hiding (_⊓_)
open import Data.Product
open import Relation.Binary.PropositionalEquality
--open import Relation.Binary
open import Data.Fin using (Fin; fromℕ; fromℕ≤; toℕ;  raise; reduce≥; inject₁) 
                     renaming (zero to f0; suc to fsuc)

open import Data.Unit
open import Data.List using (List; _∷_; [])
open import Level using () renaming (zero to Lzero)
open import Data.Vec renaming (zip to zipv; map to mapv)
open import Function

-- AOPA
open import Relations
open import Relations.Minimum
open import Relations.Coreflexive
open import Sets
open import AlgebraicReasoning.Relations

open import AlgebraicReasoning.Equality

-- END AOPA
open import Level using (Level) renaming (zero to Lzero)

open import Matrix.NonAssociativeNonRing

module Matrix.NewSpec (NAR : NonAssociativeNonRing Lzero Lzero) where

open Matrix.Abstract (NAR) using ()
open Matrix.Tri (NAR)      using (Tri; _T+_; _T*_; valiantOverlap'; foldTri; one; two; tri1; rec; tri2)
open Matrix.NewNewSplit (NAR) using (splitSize; SplitMat) renaming (splitAdd to _S+_)
open Matrix.TriFold (NAR)

--allPrevious : (k : ℕ) -> Vec (Tri s) k
 
allPrevious : ∀ {s} → Tri s → (k : ℕ) -> Vec (Tri s) k

-- Non-associative powers
_T^[1+_] : ∀ {s} → Tri s → ℕ → Tri s
_T^[1+_] {s} T i = (foldr (λ _ → Tri s) _T+_ T ∘ (mapv (uncurry (_T*_))) ∘ (uncurry′ zipv) ∘ < id , reverse >) (allPrevious T i)

--  where
--    allPrevious : ∀ {s} → Tri s → (k : ℕ) -> Vec (Tri s) k

allPrevious T zero     = []
allPrevious T (suc n') = T T^[1+ n' ] ∷ allPrevious T n'

--allPrevious zero     = []
--allPrevious (suc n') = T T^[1+ n' ] ∷ allPrevious n'

sumV : {a : Set} {n : ℕ} → (_⊕_ : a → a → a) → (0' : a) → Vec a n → a
sumV {a} _⊕_  = foldr (λ _ → a) _⊕_



⨁ : {a : Set} → (plus : a → a → a) → (n : ℕ) → (aᵢ : ℕ → a) → a
⨁ _⊕_ zero aᵢ    = aᵢ 0
⨁ _⊕_ (suc n) aᵢ = ⨁ _⊕_ n aᵢ ⊕ aᵢ (suc n)

n-is-enough : {a : Set} -> ℕ → (plus : a -> a -> a) -> (gen : ℕ -> a) -> Set
n-is-enough n _⊕_ aᵢ = (m : ℕ) → ⨁ _⊕_ n aᵢ ≡ ⨁ _⊕_ (n + m) aᵢ

-- we don't have decidable equality and stuff, maybe, so I'm not sure if it is
-- possible to work with this, even if it sounds nice!
sum-is-finite : {a : Set} -> (plus : a -> a -> a) -> (gen : ℕ -> a) -> Set
sum-is-finite _⊕_ aᵢ = ∃ (λ n → n-is-enough n _⊕_ aᵢ)

valiant-sum-is-finite : ∀ {s} → Tri s → Set
valiant-sum-is-finite A = sum-is-finite _T+_ (λ n → A T^[1+ n ])

valiant-sum : ∀ {s} → (A : Tri s) → valiant-sum-is-finite A → Tri s
valiant-sum A (n , pf) = ⨁ _T+_ n (λ k → A T^[1+ k ])

valiant-sum-n : ∀ {s} → ℕ → Tri s → Tri s
valiant-sum-n n A = ⨁ _T+_ n (λ k → A T^[1+ k ])

valiant-sum-smart : ∀ {s} → Tri s → Tri s
valiant-sum-smart {s} A = ⨁ _T+_ (splitSize s) (λ k → A T^[1+ k ])


-- specification of the overlap, using my idea (though JP began implementing, while we were talking, a while ago)

-- generates all possible bracketings with A^mCB^n

-- might be easier to just build a tree! (valiant's approach)
-- generate all trees of size m + 1 + n
-- let first m nodes be A, then 1 C, then n B

data BTree : ℕ → Set where
  tip : BTree 1
  bin : ∀ {m n} → BTree m → BTree n → BTree (m + n)
  
-- should have length catalan(n)
allTrees : (n : ℕ) → List (BTree (suc n))
allTrees zero = tip ∷ []
allTrees (suc n) = {!!}
  where 
  allPrev : (n : ℕ) → List (BTree n)
  allPrev zero = []
  allPrev (suc n') = {!!}

_^[_]*_*_^[_] : ∀ {s1 s2} → Tri s1 → ℕ → SplitMat s1 s2 → Tri s2 → ℕ → SplitMat s1 s2 
A ^[ m ]* C * B ^[ n ] = {!!}


-- multiply size of left times from left, size of right times from right.

-- powers should have all possible bracketings. Are marked by a pair of ℕ

-- could maybe be generalised, into a fold!
⨁P : {a : Set} → (plus : a → a → a) → (n : ℕ × ℕ) → (aᵢ : ℕ × ℕ → a) → a
⨁P _⊕_ (zero  , zero)  aᵢ = aᵢ (zero , zero)
⨁P _⊕_ (zero  , suc n) aᵢ = ⨁P _⊕_ (zero , n) aᵢ ⊕ aᵢ (zero , suc n)
⨁P _⊕_ (suc m , n)     aᵢ = ⨁P _⊕_ (m , n) aᵢ ⊕ aᵢ (suc m , n)

overlap-sum : ∀ {s1 s2} → Tri s1 → SplitMat s1 s2 → Tri s2 → SplitMat s1 s2
overlap-sum {s1} {s2} t1 r t2 = ⨁P _S+_ (splitSize s1 , splitSize s2) (uncurry (λ m n → t1 ^[ m ]* r * t2 ^[ n ]))



has-transitive-closure : ∀ {s} → ℙ (Tri s)
has-transitive-closure = valiant-sum-is-finite 

corefl-has-transitive-closure : ∀ {s} → Tri s ← Tri s
corefl-has-transitive-closure = has-transitive-closure ¿


--_○_ : {i k : Level} {A : Set i} {B : Set}{C : Set k} → C ← B → B ← A → C ← A
--(R ○ S) c a = ∃ (λ b → S b a × R c b)
--_◍_ : {i k : Level} {A : Set i} {B : Set}{C : Set k} → C ← B → B ← A → C ← A
--(R ◍ S) c a = ∃ (λ b → Σ (S b a) (λ x → R c b))

-- check 
-- A⁺ A
aaa : ∀ {s} → (Tri s × ℕ) ← Tri s
aaa (T₁ , n) T₂ = n-is-enough n _T+_ (λ k → T₂ T^[1+ k ]) × T₁ ≡ T₂

bbb : ∀ {s} → Tri s ← (Tri s × ℕ)
bbb = {!!}

-- takes a relation A → A and a 

-- takes a predicate and filters a thing by it.
-- _¿ 
-- in this case, predicate valiant-sum-is-finite.
-- want it to be input into function (λ pf → valiant-sum


-- skulle kunna ha valiant-sum-is-finite A = (Tri s × pf)

-- alternatives
--valiantwrapper : ∀ {s} → Σ (Tri s) valiant-sum-is-finite ← Tri s
--valiantwrapper = {!!}

specif : ∀ {s} → Tri s ← Tri s
specif A⁺ A = Σ (valiant-sum-is-finite A) (λ pf → valiant-sum A pf ≡ A⁺)


-- relation från Tri till Tri och n, och Tri och n 
-- inkludera n i 
transitiveclosure : ∀ {s} → Tri s ← Tri s
transitiveclosure {s} A⁺ A = ({!!} ○ corefl-has-transitive-closure) A⁺ A
-- sum-is-finite + 

base-case : valiant-sum-smart one ≡ one
base-case = refl

cong₃ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} {x x' : A} {y y' : B} {z z' : C} {f : A → B → C → D} → x ≡ x' → y ≡ y' → z ≡ z' → f x y z ≡ f x' y' z' 
cong₃ refl refl refl = refl

tri-proof : {s1 s2 : Splitting} {t1 t1' : Tri s1} {r r' : SplitMat s1 s2} {t2 t2' : Tri s2} → (t1 ≡ t1') → (r ≡ r') → (t2 ≡ t2') → two t1 r t2 ≡ two t1' r' t2'
tri-proof = cong₃

tri-proof' : {s1 s2 : Splitting} {t1 t2 : Tri (deeper s1 s2)} → (tri1 t1 ≡ tri1 t2) → (rec t1 ≡ rec t2) → (tri2 t1 ≡ tri2 t2) → t1 ≡ t2
tri-proof' {t1 = t1} {t2 = t2} pf1 pf2 pf3 = ≡-begin 
           t1 
             ≡⟨ sym lemma ⟩ 
           two (tri1 t1) (rec t1) (tri2 t1) 
             ≡⟨ tri-proof pf1 pf2 pf3 ⟩
           two (tri1 t2) (rec t2) (tri2 t2)
             ≡⟨ lemma ⟩
           t2 ≡∎
  where
  lemma : ∀ {s1 s2} {t : Tri (deeper s1 s2)} → two (tri1 t) (rec t) (tri2 t) ≡ t
  lemma {s1} {s2} {two T₁ R T₂} = refl

tri1-T+-commute : ∀ {s1 s2} → (t1 t2 : Tri (deeper s1 s2)) → tri1 (t1 T+ t2) ≡ (tri1 t1) T+ (tri1 t2)
tri1-T+-commute (two T₁ R T₂) (two T'₁ R' T'₂) = refl
tri2-T+-commute : ∀ {s1 s2} → (t1 t2 : Tri (deeper s1 s2)) → tri2 (t1 T+ t2) ≡ (tri2 t1) T+ (tri2 t2)
tri2-T+-commute (two T₁ R T₂) (two T'₁ R' T'₂) = refl

tri1-sum-commute : ∀ {s1 s2 n} {f : ℕ → Tri (deeper s1 s2)} → tri1 (⨁ _T+_ n f) ≡ (⨁ _T+_ n (tri1 ∘ f))
tri1-sum-commute {s1} {s2} {zero} {f} = refl
tri1-sum-commute {s1} {s2} {suc n} {f} = ≡-begin 
  tri1 ((⨁ _T+_ n f) T+ (f (suc n))) 
    ≡⟨ tri1-T+-commute (⨁ _T+_ n f) (f (suc n)) ⟩ 
  (tri1 (⨁ _T+_ n f)) T+ (tri1 (f (suc n))) 
    ≡⟨ cong₂ _T+_ (tri1-sum-commute {s1} {s2} {n} {f}) refl ⟩ 
  (⨁ _T+_ n (tri1 ∘ f)) T+ (tri1 (f (suc n))) ≡∎

tri2-sum-commute : ∀ {s1 s2 n} {f : ℕ → Tri (deeper s1 s2)} → tri2 (⨁ _T+_ n f) ≡ (⨁ _T+_ n (tri2 ∘ f))
tri2-sum-commute {s1} {s2} {zero} {f} = refl
tri2-sum-commute {s1} {s2} {suc n} {f} = ≡-begin 
  tri2 ((⨁ _T+_ n f) T+ (f (suc n))) 
    ≡⟨ tri2-T+-commute (⨁ _T+_ n f) (f (suc n)) ⟩ 
  (tri2 (⨁ _T+_ n f)) T+ (tri2 (f (suc n))) 
    ≡⟨ cong₂ _T+_ (tri2-sum-commute {s1} {s2} {n} {f}) refl ⟩ 
  (⨁ _T+_ n (tri2 ∘ f)) T+ (tri2 (f (suc n))) ≡∎

-- Non-associative powers
--_T^[1+_] : ∀ {s} → Tri s → ℕ → Tri s
--_T^[1+_] {s} T i = (foldr (λ _ → Tri s) _T+_ T ∘ (mapv (uncurry (_T*_))) ∘ (uncurry′ zipv) ∘ < id , reverse >) (allPrevious i)
--  where
--    allPrevious : (k : ℕ) -> Vec (Tri s) k
--    allPrevious zero     = []
--    allPrevious (suc n') = T T^[1+ n' ] ∷ allPrevious n'


tri1-T^-commute : ∀ {s1 s2 k} → (t1 : Tri s1) (r : SplitMat s1 s2) (t2 : Tri s2) → tri1 ((two t1 r t2) T^[1+ k ]) ≡ (tri1 (two t1 r t2)) T^[1+ k ]
tri1-T^-commute {s1} {s2} {zero} t1 r t2 = refl
tri1-T^-commute {s1} {s2} {suc n} t1 r t2 = ≡-begin 
  tri1 (two t1 r t2 T^[1+ suc n ]) 
    ≡⟨ refl ⟩ 
  tri1 ((foldr (λ _ → Tri (deeper s1 s2)) _T+_ (two t1 r t2) ∘ (mapv (uncurry (_T*_))) ∘ (uncurry′ zipv) ∘ < id , reverse >) (allPrevious (two t1 r t2) (suc n)))
    ≡⟨ {!!} ⟩ 
  tri1 ((foldr (λ _ → Tri (deeper s1 s2)) _T+_ (two t1 r t2) ∘ (mapv (uncurry (_T*_))) ∘ (uncurry′ zipv) ∘ < id , reverse >) (allPrevious (two t1 r t2) (suc n)))
    ≡⟨ {!!} ⟩ 
  ((foldr (λ _ → Tri s1) _T+_ (tri1 (two t1 r t2)) ∘ (mapv (uncurry (_T*_))) ∘ (uncurry′ zipv) ∘ < id , reverse >) (allPrevious (tri1 (two t1 r t2)) (suc n)))
    ≡⟨ refl ⟩ 
  (tri1 (two t1 r t2)) T^[1+ suc n ] ≡∎


pf-t1 : ∀ {s1 s2} (t1 : Tri s1) (r : SplitMat s1 s2) (t2 : Tri s2) → tri1 (valiant-sum-smart (two t1 r t2)) ≡ valiant-sum-smart t1
pf-t1 {s1} {s2} t1 r t2 = ≡-begin 
        tri1 (valiant-sum-smart (two t1 r t2)) 
          ≡⟨ refl ⟩
        tri1 (⨁ _T+_ (splitSize (deeper s1 s2)) (λ k → two t1 r t2 T^[1+ k ])) 
          ≡⟨ tri1-sum-commute {s1} {s2} {splitSize (deeper s1 s2)}⟩
        ⨁ _T+_ (splitSize (deeper s1 s2)) (λ k → tri1 ((two t1 r t2) T^[1+ k ]))
          ≡⟨ {!!} ⟩ -- shouldn't be a problem since we don't want function
                    -- equality, so tri1-T^-commute should be enough
        ⨁ _T+_ (splitSize (deeper s1 s2)) (λ k → ((tri1 (two t1 r t2)) T^[1+ k ]))
          ≡⟨ refl ⟩
        ⨁ _T+_ (splitSize (deeper s1 s2)) (λ k → t1 T^[1+ k ])
          ≡⟨ {!!} ⟩ -- the rest is 0
        ⨁ _T+_ (splitSize s1) (λ k → t1 T^[1+ k ])
          ≡⟨ refl ⟩
        valiant-sum-smart t1 ≡∎
--

pf-t2 : ∀ {s1 s2} (t1 : Tri s1) (r : SplitMat s1 s2) (t2 : Tri s2) → tri2 (valiant-sum-smart (two t1 r t2)) ≡ valiant-sum-smart t2
pf-t2 {s1} {s2} t1 r t2 = ≡-begin 
        tri2 (valiant-sum-smart (two t1 r t2)) 
          ≡⟨ refl ⟩
        tri2 (⨁ _T+_ (splitSize (deeper s1 s2)) (λ k → two t1 r t2 T^[1+ k ])) 
          ≡⟨ tri2-sum-commute {s1} {s2} {splitSize (deeper s1 s2)}⟩
        ⨁ _T+_ (splitSize (deeper s1 s2)) (λ k → tri2 (two t1 r t2 T^[1+ k ]))
          ≡⟨ {!!} ⟩
      
        valiant-sum-smart t2 ≡∎


ind-case : ∀ {s1 s2} {t1 : Tri s1} {r : SplitMat s1 s2} {t2 : Tri s2} → valiant-sum-smart (two t1 r t2) ≡ valiantOverlap' (valiant-sum-smart t1) r (valiant-sum-smart t2)
ind-case {t1 = t1} {r = r} {t2 = t2} = tri-proof' (pf-t1 t1 r t2) {!!} (pf-t2 t1 r t2) --tri-proof {!!} {!!} {!!}

-- fun equal
fun-⊒ : ∀ {A : Set} {B : Set} (f : A → B) (g : A → B) → (∀ a → f a ≡ g a) → fun f ⊒ fun g
fun-⊒ f g f≡g .(g a) a refl = f≡g a 

valiant-der : ∀ {s} → ∃ (λ f → specif {s} ⊒ fun f) 
valiant-der {s} = (_ , (
            ⊒-begin 
              specif 
            ⊒⟨ {!!} ⟩ -- kind of uninteresting, depends on specification
              fun valiant-sum-smart
            ⊒⟨ fun-⊒ valiant-sum-smart (foldTri one valiantOverlap') (λ a → foldTri-intro {Lzero} {Tri} {one} {valiantOverlap'} {valiant-sum-smart} {s} {a}  base-case ind-case) ⟩


              fun (foldTri one valiantOverlap')  -- as fold
     --       ⊒⟨ {!!} ⟩
     --         fun (foldTri one valiantOverlap') 
            ⊒∎))


--foldTri-intro {A = Tri} {one' = one} {f = f} {h = valiant-sum-smart} base-case ind-case


--foldTri-intro : ∀ {a} {A : Splitting → Set a} 
--  -- Stuff:
--  {one' : A one} 
--  {f : ∀ {s1' s2'} → A s1' → SplitMat s1' s2' → A s2' → A (deeper s1' s2')} 
--  {h : ∀ {s} → Tri s → A s} 
--  {s : Splitting} 
--  {t : Tri s}
--  → 
--  -- Proofs: 
--  (h one) ≡ one' → 
--  (∀ {s1} {s2} {t1 : Tri s1} 
--               {t2 : Tri s2}
--               {r  : SplitMat s1 s2} → 
--  (h (two t1 r t2)) ≡ f (h t1) r (h t2)) → 
--  -- Conclusion:
--  h t ≡ foldTri one' f t

-- to create a fold, should prove that 
-- valiant-sum-n one           == g one
-- valiant-sum-n (two T₁ S T₂) == g (valiant-sum-n T₁) S (valiant-sum-n T₂)
-- I.e., Uniqueness prop for fold. (universal property!)

-- actually 
-- valiant-sum-n α 
-- h = 《 f 》 ≡ h ∘ α = f ∘ F h
-- där α är det som gör en tripel till en tri. 
-- vill alltså visa att 
-- h one = f one
-- h (two t1 r t2) = f (two (h t1) r (h t2))



-- för F h (one) = one
-- F h (two t1 r t2) = two (h t1) r (h t2)
-- one 