-- own
open import Definitions using (_≰_; _>_; _<_)
open import NatLemmas   using (m≤sm; m≤m; p≤p)

-- standard library
open import Data.Sum                using (_⊎_) renaming (inj₁ to inj1; inj₂ to inj2)
open import Data.Integer as ℤ       using (ℤ; _+_; +_; -[1+_]; -≤+; -≤-; +≤+; _⊖_; _-_; -_; _≤?_) renaming (_⊔_ to max; _≤_ to _z≤_)
open import Data.Integer.Properties using (commutativeRing)
open import Data.Nat.Properties using (m≤m+n) renaming (≰⇒> to n≰⇒>; 
                                         commutativeSemiring to ncsr)
open import Data.Nat as ℕ using (ℕ; z≤n; s≤s) renaming (_+_ to _n+_; _≤_ to _n≤_; _≤?_ to _n≤?_; zero to nzero; suc to nsuc; _<_ to _n<_; _≰_ to _n≰_; _>_ to _n>_)
open import Data.Product using () renaming (proj₁ to proj1; proj₂ to proj2)
open import Relation.Nullary.Core using (yes; no)
open import Algebra using (CommutativeRing)
--open import Algebra.FunctionProperties using ()
open import Relation.Binary using (DecTotalOrder; _⇒_; _Preserves₂_⟶_⟶_)
open import Relation.Binary.PropositionalEquality using (cong;  _≡_) renaming (refl to eqrefl; sym to eqsym)
-- continue here! above row should be refl not eqrefl!

open Relation.Binary.PropositionalEquality.≡-Reasoning
open ℤ.≤-Reasoning renaming (begin_ to start_ ; _∎ to _□; _≡⟨_⟩_ to _≡'⟨_⟩_)
open ℕ.≤-Reasoning renaming (begin_ to nstart_ ; _∎ to _n□; _≡⟨_⟩_ to _n≡'⟨_⟩_; 
                            _≤⟨_⟩_ to _n≤⟨_⟩_ )
module ZLemmas where

open Algebra.CommutativeRing commutativeRing hiding (_+_; zero; _-_; -_)
open Algebra.CommutativeSemiring ncsr hiding (_+_ ; zero) 
     renaming (sym to nsym; +-identity to n+-identity; +-assoc to n+-assoc; 
               +-comm to n+-comm)
open Relation.Binary.DecTotalOrder ℤ.decTotalOrder renaming (refl to ≤-refl; trans to ≤-trans;
                                             _≤?_ to _z≤?_)
open Relation.Binary.DecTotalOrder ℕ.decTotalOrder hiding (_≤?_) renaming (_≤_ to _nd≤_; 
                   refl to n≤-refl; trans to n≤-trans; ≤-resp-≈ to n≤-resp-≡)


-- Three small helper lemmas to shorten proofs.


lemma : (a : ℤ) -> a ≤ a + + 1
lemma -[1+ nzero ] = start 
  -[1+ nzero ]           ≤⟨ -≤+ ⟩ 
  -[1+ nzero ] + + (ℕ.suc ℕ.zero) □
lemma -[1+ ℕ.suc a ] = start 
  -[1+ ℕ.suc a ]        ≤⟨ -≤- m≤sm ⟩ 
  -[1+ ℕ.suc a ] + + (ℕ.suc ℕ.zero) □
lemma (+ a) = start 
  + a                   ≤⟨ +≤+ m≤sm ⟩ 
  + ℕ.suc a             ≡'⟨ cong (λ x → + x) (n+-comm 1 a) ⟩
  + a + + (ℕ.suc ℕ.zero) □


lemma2 : (a : ℤ) -> a + -[1+ 0 ] ≤ a
lemma2 (+ 0)      = -≤+
lemma2 (+ nsuc a) = +≤+ m≤sm
lemma2 -[1+ a ]   = -≤- (nstart 
  a                    n≡'⟨ nsym (proj2 n+-identity a) ⟩ 
  a n+ 0               n≤⟨ m≤sm ⟩ 
  nsuc (a n+ 0) n□)

lemma3 : (a b : ℕ) -> a ⊖ nsuc b ≡ a ⊖ b + -[1+ 0 ]
lemma3 a 0 = eqrefl
lemma3 0 (nsuc b) = begin 
  -[1+ nsuc b ]    ≡⟨ cong (λ x → -[1+ nsuc x ]) (nsym (proj2 n+-identity b)) ⟩ 
  -[1+ nsuc (b n+ 0) ] ∎
lemma3 (nsuc a) (nsuc b) = lemma3 a b

-- Addition inequality
a≤a+b : (a : ℤ) (b : ℕ) -> a ≤ a + + b
a≤a+b a ℕ.zero = start 
  a              ≡'⟨ sym (proj2 +-identity a ) ⟩ 
  a + + nzero □
a≤a+b -[1+ nzero ] (ℕ.suc ℕ.zero) = start 
  -[1+ nzero ]                     ≤⟨ -≤+ ⟩ 
  -[1+ nzero ] + + (ℕ.suc ℕ.zero) □
a≤a+b -[1+ ℕ.suc a ] (ℕ.suc ℕ.zero)  = start 
  -[1+ ℕ.suc a ]                      ≤⟨ -≤- m≤sm ⟩ 
  -[1+ ℕ.suc a ] + + (ℕ.suc ℕ.zero) □
a≤a+b (+ a) (ℕ.suc ℕ.zero) = start 
  + a                       ≤⟨ +≤+ m≤sm ⟩ 
  + ℕ.suc a                 ≡'⟨ cong (λ x → + x) (n+-comm 1 a) ⟩
  + a + + (ℕ.suc ℕ.zero) □
a≤a+b a (ℕ.suc (ℕ.suc b)) = start 
  a                            ≤⟨ a≤a+b a (ℕ.suc b) ⟩ 
  a + + (ℕ.suc b)              ≤⟨ lemma (a + + (ℕ.suc b)) ⟩
  (a + + (ℕ.suc b)) + + 1      ≡'⟨ +-assoc a  (+ (ℕ.suc b)) (+ 1) ⟩
  a + (+ (ℕ.suc b) + + 1)      ≡'⟨ sym (cong (λ x → a + x) 
                                 (cong (λ x → + x) (n+-comm 1 (ℕ.suc b)))) ⟩
  a + + ℕ.suc (ℕ.suc b) □


-- Subtraction inequality
a-[1+b]≤a : (a : ℤ) (b : ℕ) -> a + -[1+ b ] ≤ a
a-[1+b]≤a (+ 0) 0             = -≤+
a-[1+b]≤a (+ nsuc a) 0        = +≤+ m≤sm
a-[1+b]≤a (+ 0)      (nsuc b) = -≤+
a-[1+b]≤a (+ nsuc a) (nsuc b) = start 
  + nsuc a + -[1+ nsuc b ]       ≡'⟨ lemma3 a b ⟩
  + nsuc a + -[1+ b ] + -[1+ 0 ] ≤⟨ lemma2 (+ nsuc a + -[1+ b ]) ⟩ 
  + nsuc a + -[1+ b ]            ≤⟨ a-[1+b]≤a (+ nsuc a) b ⟩ 
  + nsuc a □
a-[1+b]≤a -[1+ a ] b = -≤- (nstart 
  a                 n≤⟨ m≤sm ⟩ 
  (nsuc a)          n≤⟨ m≤m+n (nsuc a) b ⟩
  (nsuc a) n+ b     n≡'⟨ eqrefl ⟩
  nsuc (a n+ b) n□)

-- Not less than or equal => greater than
≰⇒> : _≰_ ⇒ _>_
≰⇒> { -[1+ n ]} { -[1+ nzero ]} pf with pf (-≤- z≤n)
... | ()
≰⇒> { -[1+ nzero ]} { -[1+ nsuc m ]} pf = -≤- z≤n
≰⇒> { -[1+ nsuc n ]} { -[1+ nsuc m ]} pf = -≤- (n≰⇒> (λ x → pf (-≤- (s≤s x))))
≰⇒> { -[1+ n ]} { + m } pf with pf -≤+ -- absurd
... | ()
≰⇒> { + n } { + m } pf = +≤+ (n≰⇒> (λ x → pf (+≤+ x)))
≰⇒> { + n } { -[1+ nzero ] } _ = +≤+ z≤n
≰⇒> { + n } { -[1+ (nsuc m) ] } pf = -≤+


-- Adding something positive increases size.
0≤b=>a≤a+b : (a b : ℤ) -> + 0 ≤ b -> a ≤ a + b
0≤b=>a≤a+b a (+ b') pf = a≤a+b a b'
0≤b=>a≤a+b a (-[1+ b' ]) pf  with pf 
...| ()

-- Adding something negative decreases size.
b≤0=>a+b≤a : (a b : ℤ) -> b ≤ + 0 -> a + b ≤ a
b≤0=>a+b≤a a (+ nzero)   pf = start a + + 0 ≡'⟨ proj2 +-identity a ⟩ a □
b≤0=>a+b≤a a (+ nsuc n) pf with pf
...| +≤+ ()
b≤0=>a+b≤a a (-[1+ b ]) pf = a-[1+b]≤a a b


-- Self inequality for ℤ
z≤z : {z : ℤ} -> z ≤ z
z≤z {+ n}       = +≤+ m≤m
z≤z { -[1+ n ]} = -≤- m≤m


-- Lemma about commutativity and associativity
lemma4 : (a b c : ℤ) -> a + b + (c - b) ≡ a + c
lemma4 a b c = begin
  a + b + (c - b)       ≡⟨ eqrefl ⟩
  (a + b) + (c - b)     ≡⟨ +-assoc a b (c - b) ⟩
  (a + (b + (c - b)))   ≡⟨ cong (λ x → a + x) (+-comm b (c - b)) ⟩
  (a + ((c - b) + b))   ≡⟨ cong (λ x → a + x) (+-assoc c (- b) b) ⟩
  (a + (c + (- b + b))) ≡⟨ cong (λ x → a + (c + x)) (proj1 -‿inverse b) ⟩
  (a + (c + + 0))       ≡⟨ cong (λ x → a + x) (proj2 +-identity c) ⟩
  a + c ∎
open import Data.Empty

-- Adding one to each side preserves an inequality!
++≤++ : {a b : ℤ} -> a ≤ b -> a + + 1 ≤ b + + 1
++≤++ { -[1+ nzero ]} { -[1+ nzero ]} (-≤- pf) = +≤+ z≤n
++≤++ { -[1+ nzero ]} { -[1+ nsuc b ]} (-≤- ())
++≤++ { -[1+ nsuc a ]} { -[1+ nzero ]} (-≤- pf) = -≤+
++≤++ { -[1+ nsuc a ]} { -[1+ nsuc b ]} (-≤- pf) = -≤- (p≤p pf)
++≤++ { -[1+ nzero ]} {+ b} (-≤+) = +≤+ z≤n
++≤++ { -[1+ nsuc a ]} {+ b} (-≤+) = -≤+
++≤++ {+ a} {+ b} (+≤+ pf) = +≤+ (nstart 
  a n+ 1 n≡'⟨ n+-comm a 1 ⟩ 
  nsuc a n≤⟨ s≤s pf ⟩ 
  nsuc b n≡'⟨ n+-comm 1 b ⟩ 
  b n+ 1 n□)
++≤++ {+ a} { -[1+ b ]} ()

-- Subtracting one from both sides preserves an inequlity!
pre≤pre : {a b : ℤ} -> a ≤ b -> a - + 1 ≤ b - + 1
pre≤pre { -[1+ a ]} { -[1+ nzero ]} _ = -≤- (s≤s z≤n)
pre≤pre { -[1+ a ]} { -[1+ nsuc b ]} (-≤- pf) = -≤- (s≤s (nstart 
  nsuc (b n+ 0) n≡'⟨ cong nsuc (proj2 n+-identity b) ⟩
  nsuc b n≤⟨ pf ⟩
  a n≡'⟨ nsym (proj2 n+-identity a ) ⟩
  a n+ 0 n□
  ))
pre≤pre { -[1+ a ]}  { + nzero}   _        = -≤- z≤n
pre≤pre { -[1+ a ]}  { + nsuc b} _        = -≤+
pre≤pre { + a }      { -[1+ b ]} ()
pre≤pre { + nzero }   {+ 0}       _        = -≤- z≤n
pre≤pre { + nzero }   {+ nsuc b}  _        = -≤+
pre≤pre { + nsuc a } {+ nzero}    (+≤+ ())
pre≤pre { + nsuc a } {+ nsuc b}  (+≤+ pf) = +≤+ (p≤p pf)



-- Lemma for proving that + preserves inequalities
a≤b=>a+c≤b+c : {a b : ℤ} (c : ℤ) -> a ≤ b -> a + c ≤ b + c
a≤b=>a+c≤b+c {a} {b} (+ 0) pf = start 
  a + + 0            ≡'⟨ proj2 +-identity a ⟩ 
  a                  ≤⟨ pf ⟩
  b                  ≡'⟨ sym (proj2 +-identity b) ⟩
  b + + 0 □ 
a≤b=>a+c≤b+c {a} {b} (+ nsuc c) pf = start 
  a + + nsuc c       ≡'⟨ eqrefl ⟩
  a + (+ 1 + + c)    ≡'⟨ sym (+-assoc a (+ 1) (+ c)) ⟩
  (a + + 1) + + c    ≤⟨ a≤b=>a+c≤b+c (+ c) (++≤++ pf) ⟩
  (b + + 1) + + c    ≡'⟨ +-assoc b (+ 1) (+ c) ⟩
  b + (+ 1 + + c)    ≡'⟨ eqrefl ⟩
  b + + nsuc c □
a≤b=>a+c≤b+c {+ 0} {+ 0}           (-[1+ 0 ]) pf       = -≤- z≤n 
a≤b=>a+c≤b+c {+ 0} {+ nsuc b}      (-[1+ 0 ]) pf       = -≤+ 
a≤b=>a+c≤b+c {+ nsuc a} {+ 0}      (-[1+ 0 ]) (+≤+ ())
a≤b=>a+c≤b+c {+ nsuc a} {+ nsuc b} (-[1+ 0 ]) (+≤+ pf) = +≤+ (p≤p pf) 

a≤b=>a+c≤b+c {+ a}       { -[1+ b ]} (-[1+ 0 ]) ()
a≤b=>a+c≤b+c { -[1+ a ]} { -[1+ b ]} (-[1+ 0 ]) (-≤- pf) = -≤- (s≤s (nstart 
  b n+ 0 n≡'⟨ proj2 n+-identity b ⟩ 
  b      n≤⟨ pf ⟩ 
  a      n≡'⟨ nsym (proj2 n+-identity a) ⟩  --- ask somebody, why does it work 
                                           --- with +-comm 0 a
  a n+ 0 n□)) 
a≤b=>a+c≤b+c { -[1+ a ]} {+ nzero}   (-[1+ 0 ])      (-≤+) = -≤- z≤n 
a≤b=>a+c≤b+c { -[1+ a ]} {+ nsuc b} (-[1+ 0 ])      (-≤+) = -≤+ 
a≤b=>a+c≤b+c {a}         {b}        (-[1+ nsuc c ]) pf    = start 
  a + -[1+ nsuc c ]        ≡'⟨ sym (+-assoc a (- (+ 1)) -[1+ c ]) ⟩
  a - + 1 + -[1+ c ]       ≤⟨ a≤b=>a+c≤b+c -[1+ c ] (pre≤pre pf) ⟩ 
  b - + 1 + -[1+ c ]       ≡'⟨ +-assoc b (- (+ 1)) ( -[1+ c ]) ⟩ 
  b + -[1+ nsuc c ] □

-- Transforms an inequality into an inequality with 0
to0≤ : {a b : ℤ} -> a ≤ b -> + 0 ≤ b - a
to0≤ {a} {b} pf = start 
  + 0 ≡'⟨ sym (proj2 -‿inverse a) ⟩ 
  a - a ≤⟨ a≤b=>a+c≤b+c (- a) pf ⟩ 
  b - a □

-- Very useful! It is ok to add two inequalities together!
_z+-mono_ : _+_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
_z+-mono_ {m1} {m2} {n1} {n2} m1≤m2 n1≤n2 = start
  m1 + n1             ≡'⟨ +-comm m1 n1 ⟩    
  n1 + m1             ≤⟨ 0≤b=>a≤a+b (n1 + m1) (m2 - m1) (to0≤ m1≤m2) ⟩
  n1 + m1 + (m2 - m1) ≡'⟨ lemma4 n1 m1 m2 ⟩ 
  n1 + m2             ≡'⟨ +-comm n1 m2 ⟩
  m2 + n1             ≤⟨ 0≤b=>a≤a+b (m2 + n1) (n2 - n1) (to0≤ n1≤n2) ⟩
  m2 + n1 + (n2 - n1) ≡'⟨ lemma4 m2 n1 n2 ⟩
  m2 + n2 □


-- Multiply inequality by -1
negate≤ : {a b : ℤ} -> a ≤ b -> - b ≤ - a
negate≤ { -[1+ a ]} { -[1+ b ]} (-≤- pf) = +≤+ (s≤s pf)
negate≤ { -[1+ a ]} { + nzero}   _        = +≤+ z≤n
negate≤ { -[1+ a ]} { + nsuc b} _        = -≤+
negate≤ {+ a}       { -[1+ b ]} ()
negate≤ {+ nzero}    {+ nzero}    (+≤+ pf) = +≤+ z≤n
negate≤ {+ nsuc a}  {+ nzero}    (+≤+ ())
negate≤ {+ nzero}    {+ nsuc b}  (+≤+ pf) = -≤+
negate≤ {+ nsuc a}  {+ nsuc b}  (+≤+ pf) = -≤- (p≤p pf)


-- If a + b < c + d, then either a < c or b < d
less_sum_has_less : {l1 l2 g1 g2 : ℤ} -> l1 + l2 < g1 + g2 -> (l1 < g1) ⊎ (l2 < g2)
less_sum_has_less {l1} {l2} {g1} {g2} ineq with g1 ≤? l1
...| yes pf = inj2 (start 
  + 1 + l2               ≡'⟨ sym (proj2 +-identity (+ 1 + l2)) ⟩ 
  + 1 + l2 + + 0         ≡'⟨ sym (cong (λ x → + 1 + l2 + x) 
                                 (proj2 -‿inverse l1)) ⟩ 
  (+ 1 + l2) + (l1 - l1) ≡'⟨ sym (+-assoc (+ 1 + l2) l1 (- l1)) ⟩ 
  ((+ 1 + l2) + l1) - l1 ≡'⟨ cong (λ x → x - l1) (+-assoc (+ 1) l2 l1) ⟩ 
  + 1 + (l2 + l1) - l1   ≡'⟨ cong (λ x → + 1 + x - l1) (+-comm l2 l1) ⟩
  + 1 + (l1 + l2) - l1   ≤⟨ ineq z+-mono negate≤ pf ⟩ 
  (g1 + g2) - g1         ≡'⟨ +-comm (g1 + g2) (- g1) ⟩ 
  - g1 + (g1 + g2)       ≡'⟨ sym (+-assoc (- g1) g1 g2) ⟩ 
  - g1 + g1 + g2         ≡'⟨ cong (λ x → x + g2) (proj1 -‿inverse g1) ⟩ 
  + 0 + g2               ≡'⟨ proj1 +-identity g2 ⟩
  g2 □)
...| no  pf = inj1 (≰⇒> pf)



-- Greater than implies not less than or equal
>⇒≰ : {a b : ℤ} -> a > b -> a ≰ b
>⇒≰ {a} {b} a>b a≤b with start 
  + 0             ≡'⟨ sym (proj2 -‿inverse a) ⟩ 
  a - a           ≤⟨ a≤b z+-mono z≤z ⟩
  b - a           ≤⟨ (start 

           b                 ≡'⟨ sym (proj1 +-identity b) ⟩ 
           + 0 + b           ≡'⟨ eqrefl ⟩ 
           - + 1 + + 1 + b   ≡'⟨ +-assoc (- (+ 1)) (+ 1) b ⟩ 
           - + 1 + (+ 1 + b) ≤⟨ (z≤z { - + 1})  z+-mono a>b ⟩ 
           - + 1 + a         ≡'⟨ +-comm (- (+ 1)) a ⟩
           a - + 1 □) z+-mono z≤z ⟩

  (a - + 1) - a   ≡'⟨ +-comm (a - + 1) (- a) ⟩
  - a + (a - + 1) ≡'⟨ sym (+-assoc (- a) a (- (+ 1))) ⟩
  - a + a - + 1   ≡'⟨ cong (λ x → x - + 1) (proj1 -‿inverse a) ⟩
  + 0 - + 1       ≡'⟨ eqrefl ⟩
  -[1+ 0 ] □
...| ()