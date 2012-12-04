module Matrix.JP.JP4
   a
   ( _+_ : a -> a -> a )
   ( _·_ : a -> a -> a ) 
   ( _≥_ : a -> a -> Set ) 
   ( ≥-refl : ∀ {a} -> a ≥ a ) 
   (≥-mono : ∀ {x y z} -> x ≥ (y + z) → x ≥ y)
 where

open import Data.Nat renaming (_+_ to _+ℕ_; _≥_ to  _≥ℕ_ )
open import Data.Fin using (Fin; fromℕ; fromℕ≤; toℕ;  raise; reduce≥) 
                     renaming (zero to f0; suc to fsuc)

open import Data.Unit hiding (_≤?_)
open import Data.Empty
open import Data.Product -- using (∃) renaming (_,_ to _,:_)
open import Function
open import Relation.Nullary.Core

open import Relation.Binary using (Setoid; Preorder)

open import Relation.Binary.PropositionalEquality

import Relation.Binary.EqReasoning as EqR
import Relation.Binary.PreorderReasoning as PreR

Matrix : ℕ -> ℕ -> Set
Matrix m n = Fin m -> Fin n -> a


data Splitting : ℕ -> Set where
  empty : Splitting 0
  one : Splitting 0
  deeper : ∀ {n} -> Splitting n -> Splitting n -> Splitting (suc n)

data Mat : {n : ℕ} -> Splitting n -> Splitting n → Set where
  one : (x : a) -> Mat one one
  zero : ∀ {n} {s s' : Splitting n} -> Mat s s'
  quad : ∀ {n} {r1 r2 c1 c2 : Splitting n} -> (m11 : Mat r1 c1) -> (m12 : Mat r1 c2) -> 
                            (m21 : Mat r2 c1) -> (m22 : Mat r2 c2) 
          -> Mat (deeper r1 r2) (deeper c1 c2)

IsZero : ∀ {n} {s s' : Splitting n} -> Mat s s' -> Set 
IsZero t = t ≡ zero 

IsTriangle : ∀ {n} {s : Splitting n} -> Mat s s -> Set
IsTriangle (one x) = ⊥ -- not upper triangular
IsTriangle zero = ⊤
IsTriangle (quad t₁ t₂ q t₃) = IsTriangle t₁ × IsZero q × IsTriangle t₃

Tri : ∀ {n} -> (s : Splitting n) -> Set
Tri s = ∃ \(x : Mat s s) -> IsTriangle x

infixl 4 _⊇_ _≅_
_⊇_ : ∀ {n} {s1 s2 : Splitting n} -> Mat s1 s2 -> Mat s1 s2 -> Set
x ⊇ zero = ⊤
zero ⊇ _ = ⊥
one x ⊇ one x₁ = x ≥ x₁
quad x x₁ x₂ x₃ ⊇ quad y y₁ y₂ y₃ = x ⊇ y × x₁ ⊇ y₁ × x₂ ⊇ y₂ × x₃ ⊇ y₃


-- custom pair so that inference works.
record _≅_ {n} {s1 s2 : Splitting n} (A B : Mat s1 s2) : Set where
  constructor _/_
  field 
       ⟶ : A ⊇ B
       ⟵ : B ⊇ A
open _≅_

⊇-refl : ∀ {n} {s1 s2 : Splitting n} -> (y : Mat s1 s2) -> y ⊇ y
⊇-refl (one x) =  ≥-refl
⊇-refl zero = tt
⊇-refl (quad y y₁ y₂ y₃) = ⊇-refl y , ⊇-refl y₁ , ⊇-refl y₂ , ⊇-refl y₃

≅-refl : ∀ {n} {s1 s2 : Splitting n} -> {y : Mat s1 s2} -> y ≅ y
≅-refl {y = y} = (⊇-refl y) / (⊇-refl y)

≅-sym : ∀ {n} {s1 s2 : Splitting n} -> {x y : Mat s1 s2} -> x ≅ y -> y ≅ x
≅-sym (pro₁ / pro₂) = pro₂ / pro₁

⊇-preorder : ∀ {n} {s1 s2 : Splitting n} ->  Preorder _ _ _
⊇-preorder {n} {s1} {s2} = record { Carrier = Mat s1 s2; _≈_ = _≅_; _∼_ = _⊇_; isPreorder = {!!} }

≅-setoid : ∀ {n} {s1 s2 : Splitting n} -> Setoid _ _
≅-setoid {n} {s1} {s2}= record { Carrier = Mat s1 s2; _≈_ = _≅_; 
                                 isEquivalence = record { refl = ≅-refl; 
                                                          sym =  ≅-sym  ;
                                                          trans = {!!} } }

module ⊇-Reasoning where
  private
    module Dummy {n} {s1 s2 : Splitting n} where
      open PreR (⊇-preorder {n} {s1} {s2}) public
  open Dummy public

module ≅-Reasoning where
  private
    module Dummy {n} {s1 s2 : Splitting n} where
      open EqR (≅-setoid {n} {s1} {s2}) public
        hiding (_≡⟨_⟩_) renaming (_≈⟨_⟩_ to _≅⟨_⟩_)
  open Dummy public



infixl 6 _∪_
_∪_ : ∀ {n} {s1 s2 : Splitting n} -> Mat s1 s2 -> Mat s1 s2 -> Mat s1 s2
zero ∪ x = x
x ∪ zero = x
one x ∪ one x₁ = one (x + x₁)
quad x x₁ x₂ x₃ ∪ quad y y₁ y₂ y₃ = quad (x ∪ y) (x₁ ∪ y₁) (x₂ ∪ y₂) (x₃ ∪ y₃)


infix 7 _∙_
_∙_ : ∀ {n} {s1 s2 s3 : Splitting n} -> Mat s1 s2 -> Mat s2 s3 -> Mat s1 s3
zero ∙ x = zero
x ∙ zero = zero
one x ∙ one y = one (x · y)
quad x11 x12 x21 x22 ∙ quad y11 y12 y21 y22 = 
  quad ((x11 ∙ y11) ∪ (x12 ∙ y21)) ((x11 ∙ y12) ∪ (x12 ∙ y22)) 
       ((x21 ∙ y11) ∪ (x22 ∙ y21)) ((x21 ∙ y12) ∪ (x22 ∙ y22)) 


Good : ∀ {n} {s1 s2 : Splitting n} -> Mat s1 s1 -> Mat s1 s2 -> Mat s2 s2 -> Mat s1 s2 -> Set
Good A C B X = X ⊇ C × A ∙ X ∪ X ∙ B ∪ X ≅ X

_ClosureOf_ : ∀ {n} {s : Splitting n} -> Mat s s -> Mat s s -> Set
X ClosureOf C = X ⊇ C × X ∙ X ∪ X ≅ X

Good' : ∀ {n} {s1 s2 : Splitting n} -> Tri s1 -> Mat s1 s2 -> Tri s2 -> Mat s1 s2 -> Set
Good' (A , _) C (B , _) X = Good A C B X

cong₄ : ∀ {n} {s1 s2 s3 s4 : Splitting n}
        {a1 a2 : Mat s1 s3} {b1 b2} {c1 c2} {d1 d2 : Mat s2 s4} → 
        a1 ≅ a2 → b1 ≅ b2 → c1 ≅ c2 → d1 ≅ d2 → quad a1 b1 c1 d1 ≅ quad a2 b2 c2 d2
cong₄ (ap / aq) (bp / bq) (cp / cq) (dp / dq) = (ap , bp , cp , dp) / (aq , bq , cq , dq)

zero∪ : ∀ {n} {s1 s2 : Splitting n} -> (x : Mat s1 s2) -> x ∪ zero ≅ x
zero∪ (one x) = ≥-refl / ≥-refl
zero∪ zero = tt / tt
zero∪ (quad x x₁ x₂ x₃) = cong₄ ≅-refl ≅-refl ≅-refl ≅-refl

mono : ∀ {n} {s1 s2 : Splitting n} -> (A B C : Mat s1 s2) -> A ⊇ (B ∪ C)  → A ⊇ B
mono A zero C p = tt
mono A B zero p = begin A ∼⟨ p ⟩ B ∪ zero ≈⟨ zero∪ B ⟩ B  ∎
  where open ⊇-Reasoning
mono zero (one x) (one x₁) p = p
mono zero (quad B B₁ B₂ B₃) (quad C C₁ C₂ C₃) p = p
mono (one x) (one x₁) (one x₂) p = ≥-mono p
mono (quad A A₁ A₂ A₃) (quad B B₁ B₂ B₃) (quad C C₁ C₂ C₃) (p , p₁ , p₂ , p₃) = 
  (mono A B C p) , mono A₁ B₁ C₁ p₁ , mono A₂ B₂ C₂ p₂ , mono A₃ B₃ C₃ p₃


split : ∀ {n} {s1 s2 : Splitting n} -> (A B C : Mat s1 s2) -> A ⊇ B -> A ⊇ C -> A ⊇ B ∪ C
split A zero C p q = q
split A B zero p q = begin A ∼⟨ p ⟩ B  ≈⟨  ≅-sym (zero∪ B) ⟩ B ∪ zero  ∎
  where open ⊇-Reasoning
split zero (one x) C () q
split zero (quad B B₁ B₂ B₃) C () q
split (one x) (one x₁) (one x₂) p q = {!!}
split (quad A A₁ A₂ A₃) (quad B B₁ B₂ B₃) (quad C C₁ C₂ C₃) (p1 , p2 , p3 , p4) (q1 , q2 , q3 , q4)
  = split A B C p1 q1 , split A₁ B₁ C₁ p2 q2 , split A₂ B₂ C₂ p3 q3 , split A₃ B₃ C₃ p4 q4

valiantOverlap' : ∀ {n} {s1 s2 : Splitting n} -> (A : Tri s1) -> (C : Mat s1 s2) -> (B : Tri s2) -> ∃ \X -> Good' A C B X
valiantOverlap' (A , _) zero (B , _) = zero , tt , (begin 
   A ∙ zero ∪ zero ∙ B ∪ zero 
     ≅⟨ zero∪ _ ⟩
  A ∙ zero ∪ zero ∙ B 
     ≅⟨ zero∪ _ ⟩
  A ∙ zero 
     ≅⟨ {!!} ⟩
  zero 
     ∎)
  where open ≅-Reasoning

valiantOverlap' (one x , ()) (one x₁) _
valiantOverlap'  _ (one x) (one x₁ , ()) 
valiantOverlap' (zero , α) (one x) (zero , β) = one x , ≥-refl , ≅-refl
valiantOverlap' (zero , α) (quad C C₁ C₂ C₃) (B , β) = {!!}
valiantOverlap' (A , α) (quad C C₁ C₂ C₃) (zero , β) = {!!}
valiantOverlap' (quad A11 A12 .zero A22 , α11 , refl , α22) (quad C11 C12 C21 C22)
                (quad B11 B12 .zero B22 , β11 , refl , β22)  
   with valiantOverlap' (A22 , α22) C21 (B11 , β11)
... | x21 , ξ21 , ξ21' with valiantOverlap' (A11 , α11) (C11 ∪ A12 ∙ x21) (B11 , β11) 
                          | valiantOverlap' (A22 , α22) (C22 ∪ x21 ∙ B12) (B22 , β22)
... | x11 , ξ11 , ξ11' | x22 , ξ22 , ξ22' with valiantOverlap' (A11 , α11) (C12 ∪ A12 ∙ x22 ∪ x11 ∙ B12) (B22 , β22)
... | x12 , ξ12 , ξ12'  = quad x11 x12 x21 x22 , 
    (mono x11 C11 _ ξ11 , 
     mono x12 C12 (A12 ∙ x22) (mono x12 (C12 ∪ A12 ∙ x22) (x11 ∙ B12) ξ12) , 
     ξ21 , 
     mono x22 C22 _ ξ22) , 
     ({!mono!} , {!mono!} , {!mono!} , {!mono!}) / 
     ({!!} , {!!} , 
       ( split x21 (A22 ∙ x21 ∪ (x21 ∙ B11 ∪ x22 ∙ zero)) x21 (begin 
        x21 
           ∼⟨  mono x21 (A22 ∙ x21 ∪ x21 ∙ B11) x21 (⟵ ξ21')  ⟩ 
        A22 ∙ x21 ∪ x21 ∙ B11 
           ≈⟨ {!!} ⟩ 
        A22 ∙ x21 ∪ x21 ∙ B11 ∪ x22 ∙ zero
           ≈⟨ {!!} ⟩ 
        A22 ∙ x21 ∪ (x21 ∙ B11 ∪ x22 ∙ zero)
           ∎)) (⊇-refl x21) , 
       split x22 (A22 ∙ x22 ∪ (x21 ∙ B12 ∪ x22 ∙ B22)) x22 
          (   begin 
           x22 
              ∼⟨ split x22 (x21 ∙ B12) (A22 ∙ x22 ∪ x22 ∙ B22) 
                    {!mono ξ22!} 
                    (mono x22 (A22 ∙ x22 ∪ x22 ∙ B22) x22 (⟵ ξ22')) ⟩
           (x21 ∙ B12) ∪ (A22 ∙ x22 ∪ x22 ∙ B22)
              ≈⟨ {!!} ⟩
           A22 ∙ x22 ∪ (x21 ∙ B12 ∪ x22 ∙ B22)
              ∎) 
          (⊇-refl x22)
     )
  where open ⊇-Reasoning

valiant : ∀ {n} {s : Splitting n} -> (m : Mat s s) -> IsTriangle m -> ∃ \x -> IsTriangle x × x ClosureOf m
valiant (one x) ()
valiant zero t = zero , tt , tt , (tt / tt)
valiant (quad A C .zero B) (α , refl , β) with valiant A α | valiant B β
... | (A' , ta , α' , α'') | (B' , tb , β' , β'')  with valiantOverlap' (A' , ta) C (B' , tb) 
... | (X , ξ , ξ') = quad A' X zero B' , (ta , refl , tb) , 
                      (α' , ξ , tt , β') , cong₄ ({!mono!} / {!α''!}) ξ' {!!} β''

