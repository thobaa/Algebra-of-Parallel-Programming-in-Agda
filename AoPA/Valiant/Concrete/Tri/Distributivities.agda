open import Valiant.Abstract.NonAssociativeNonRing
open import Data.Product using (proj₁; proj₂; Σ; _,_)
open import Algebra.FunctionProperties using (_DistributesOver_)


module Valiant.Concrete.Tri.Distributivities {l₁ l₂} (NAR : NonAssociativeNonRing l₁ l₂) where



import Valiant.Helper.Definitions
open Valiant.Helper.Definitions NAR

import Valiant.Concrete.Tri
open Valiant.Concrete.Tri NAR
import Valiant.Concrete.Tri.Operations
open Valiant.Concrete.Tri.Operations NAR

import Valiant.Concrete.Mat
open Valiant.Concrete.Mat NAR
import Valiant.Concrete.Mat.Operations
open Valiant.Concrete.Mat.Operations NAR

import Valiant.Concrete.Tri.Equalities 
open Valiant.Concrete.Tri.Equalities NAR
import Valiant.Concrete.Tri.CommutativeMonoid
open Valiant.Concrete.Tri.CommutativeMonoid NAR renaming (commutativeMonoidM to cmm; commutativeMonoidV to cmv)


open NonAssociativeNonRing NAR using (_≈_) renaming (refl to ≈refl; sym to ≈sym; trans to ≈trans; +-assoc to R+-assoc; +-comm to R+-comm; +-identity to R+-identity; +-cong to R+-cong; *-cong to R*-cong; distrib to R-distrib; +-commutativeMonoid to cmr)

∙-distribˡ : ∀ {s} → (u v w : Vec s) → u ∙ (v ⊕ w) ≈ u ∙ v R+ u ∙ w
∙-distribˡ (one x) (one y) (one z) = proj₁ R-distrib x y z
∙-distribˡ (two u₁ v₁) (two u₂ v₂) (two u₃ v₃) = rearrangeLemma' {cm = cmr} (u₁ ∙ (u₂ ⊕ u₃)) (v₁ ∙ (v₂ ⊕ v₃)) (u₁ ∙ u₂) (u₁ ∙ u₃) (v₁ ∙ v₂) (v₁ ∙ v₃) (∙-distribˡ u₁ u₂ u₃) (∙-distribˡ v₁ v₂ v₃)

∙-distribʳ : ∀ {s} → (u v w : Vec s) → (u ⊕ v) ∙ w ≈ u ∙ w R+ v ∙ w
∙-distribʳ (one x) (one y) (one z) = proj₂ R-distrib z x y
∙-distribʳ (two u₁ v₁) (two u₂ v₂) (two u₃ v₃) = rearrangeLemma' {cm = cmr} ((u₁ ⊕ u₂) ∙ u₃) ((v₁ ⊕ v₂) ∙ v₃) (u₁ ∙ u₃) (u₂ ∙ u₃) (v₁ ∙ v₃) (v₂ ∙ v₃) (∙-distribʳ u₁ u₂ u₃) (∙-distribʳ v₁ v₂ v₃)

|⊛-distribˡ : ∀ {s} → (u : Vec s) (x y : R) → u |⊛ (x R+ y) v≈ u |⊛ x ⊕ u |⊛ y
|⊛-distribˡ (one x) y z = one-eq (proj₁ R-distrib x y z)
|⊛-distribˡ (two u v) x y = two-eq (|⊛-distribˡ u x y) (|⊛-distribˡ v x y)

|⊛-distribʳ : ∀ {s} → (u v : Vec s) (x : R) → (u ⊕ v) |⊛ x v≈ u |⊛ x ⊕ v |⊛ x
|⊛-distribʳ (one x) (one y) z = one-eq (proj₂ R-distrib z x y)
|⊛-distribʳ (two u v) (two u' v') x = two-eq (|⊛-distribʳ u u' x) (|⊛-distribʳ v v' x)

⊛|-distribˡ : ∀ {s} → (x : R) (u v : Vec s) → x ⊛| (u ⊕ v)  v≈ x ⊛| u ⊕ x ⊛| v
⊛|-distribˡ x (one y) (one z) = one-eq (proj₁ R-distrib x y z)
⊛|-distribˡ x (two u v) (two u' v') = two-eq (⊛|-distribˡ x u u') (⊛|-distribˡ x v v')

⊛|-distribʳ : ∀ {s} → (x y : R) (v : Vec s) → (x R+ y) ⊛| v  v≈ x ⊛| v ⊕ y ⊛| v
⊛|-distribʳ x y (one z) = one-eq (proj₂ R-distrib z x y)
⊛|-distribʳ x y (two u v) = two-eq (⊛|-distribʳ x y u) (⊛|-distribʳ x y v)

*|-distribˡ : ∀ {s₁ s₂} → (x : Mat s₁ s₂) (u v : Vec s₂) → x *| (u ⊕ v) v≈ x *| u ⊕ x *| v
*|-distribˡ (Sing x) (one y) (one z) = one-eq (proj₁ R-distrib x y z)
*|-distribˡ (RVec u) v w = one-eq (∙-distribˡ u v w)
*|-distribˡ (CVec u) (one x) (one y) = |⊛-distribˡ u x y
*|-distribˡ (quad A B C D) (two u v) (two u' v') = two-eq 
    (rearrangeLemma' {cm = cmv} (A *| (u ⊕ u')) (B *| (v ⊕ v')) (A *| u) (A *| u') (B *| v) (B *| v') (*|-distribˡ A u u') (*|-distribˡ B v v')) 
    (rearrangeLemma' {cm = cmv} (C *| (u ⊕ u')) (D *| (v ⊕ v')) (C *| u) (C *| u') (D *| v) (D *| v') (*|-distribˡ C u u') (*|-distribˡ D v v')) 

*|-distribʳ : ∀ {s₁ s₂} → (x y : Mat s₁ s₂) (v : Vec s₂) → (x + y) *| v v≈ x *| v ⊕ y *| v
*|-distribʳ (Sing x) (Sing y) (one z) = one-eq (proj₂ R-distrib z x y)
*|-distribʳ (RVec (two u₁ v₁)) (RVec (two u₂ v₂)) (two u₃ v₃) = one-eq (rearrangeLemma' {cm = cmr} ((u₁ ⊕ u₂) ∙ u₃) ((v₁ ⊕ v₂) ∙ v₃) (u₁ ∙ u₃) (u₂ ∙ u₃) (v₁ ∙ v₃) (v₂ ∙ v₃) (∙-distribʳ u₁ u₂ u₃) (∙-distribʳ v₁ v₂ v₃))
*|-distribʳ (CVec u) (CVec v) (one x) = |⊛-distribʳ u v x
*|-distribʳ (quad A B C D) (quad A' B' C' D') (two u v) = two-eq (rearrangeLemma' {cm = cmv} ((A + A') *| u) ((B + B') *| v) (A *| u) (A' *| u) (B *| v) (B' *| v) (*|-distribʳ A A' u) (*|-distribʳ B B' v)) (rearrangeLemma' {cm = cmv} ((C + C') *| u) ((D + D') *| v) (C *| u) (C' *| u) (D *| v) (D' *| v)(*|-distribʳ C C' u) (*|-distribʳ D D' v))

⊛-distribˡ : ∀ {s₁ s₂} → (u : Vec s₁) (v w : Vec s₂) → u ⊛ (v ⊕ w) m≈ u ⊛ v + u ⊛ w
⊛-distribˡ (one x) (one y) (one z) = Sing-eq (proj₁ R-distrib x y z)
⊛-distribˡ (one x) (two u v) (two u' v') = RVec-eq (two-eq (⊛|-distribˡ x u u') (⊛|-distribˡ x v v'))
⊛-distribˡ (two u v) (one x) (one y) = CVec-eq (two-eq (|⊛-distribˡ u x y) (|⊛-distribˡ v x y))
⊛-distribˡ (two u₁ v₁) (two u₂ v₂) (two u₃ v₃) = quad-eq (⊛-distribˡ u₁ u₂ u₃) (⊛-distribˡ u₁ v₂ v₃) (⊛-distribˡ v₁ u₂ u₃) (⊛-distribˡ v₁ v₂ v₃) 

⊛-distribʳ : ∀ {s₁ s₂} → (u v : Vec s₁) (w : Vec s₂) → (u ⊕ v) ⊛ w m≈ u ⊛ w + v ⊛ w
⊛-distribʳ (one x) (one y) (one z) = Sing-eq (proj₂ R-distrib z x y)
⊛-distribʳ (one x) (one y) (two u v) = RVec-eq (two-eq (⊛|-distribʳ x y u) (⊛|-distribʳ x y v))
⊛-distribʳ (two u v) (two u' v') (one x) = CVec-eq (two-eq (|⊛-distribʳ u u' x) (|⊛-distribʳ v v' x))
⊛-distribʳ (two u₁ v₁) (two u₂ v₂) (two u₃ v₃) = quad-eq (⊛-distribʳ u₁ u₂ u₃) (⊛-distribʳ u₁ u₂ v₃) (⊛-distribʳ v₁ v₂ u₃) (⊛-distribʳ v₁ v₂ v₃)

|*-distribˡ : ∀ {s₁ s₂} → (v : Vec s₁) (x y : Mat s₁ s₂) → v |* (x + y) v≈ v |* x ⊕ v |* y
|*-distribˡ (one x) (Sing y) (Sing z) = one-eq (proj₁ R-distrib x y z)
|*-distribˡ (one x) (RVec u) (RVec v) = ⊛|-distribˡ x u v
|*-distribˡ (two u v) (CVec w₁) (CVec w₂) = one-eq (∙-distribˡ (two u v) w₁ w₂)
|*-distribˡ (two u v) (quad A B C D) (quad A' B' C' D') = two-eq (rearrangeLemma' {cm = cmv} (u |* (A + A')) (v |* (C + C')) (u |* A) (u |* A') (v |* C) (v |* C') (|*-distribˡ u A A') (|*-distribˡ v C C')) (rearrangeLemma' {cm = cmv} (u |* (B + B')) (v |* (D + D')) (u |* B) (u |* B') (v |* D) (v |* D') (|*-distribˡ u B B') (|*-distribˡ v D D'))

|*-distribʳ : ∀ {s₁ s₂} → (u v : Vec s₁) (x : Mat s₁ s₂) → (u ⊕ v) |* x v≈ u |* x ⊕ v |* x
|*-distribʳ (one x) (one y) (Sing z) = one-eq (proj₂ R-distrib z x y)
|*-distribʳ (one x) (one y) (RVec v) = ⊛|-distribʳ x y v
|*-distribʳ (two u₁ v₁) (two u₂ v₂) (CVec (two u₃ v₃)) = one-eq (rearrangeLemma' {cm = cmr} ((u₁ ⊕ u₂) ∙ u₃) ((v₁ ⊕ v₂) ∙ v₃) (u₁ ∙ u₃) (u₂ ∙ u₃) (v₁ ∙ v₃) (v₂ ∙ v₃) (∙-distribʳ u₁ u₂ u₃) (∙-distribʳ v₁ v₂ v₃))
|*-distribʳ (two u v) (two u' v') (quad A B C D) = two-eq (rearrangeLemma' {cm = cmv} ((u ⊕ u') |* A) ((v ⊕ v') |* C) (u |* A) (u' |* A) (v |* C) (v' |* C) (|*-distribʳ u u' A) (|*-distribʳ v v' C)) (rearrangeLemma' {cm = cmv} ((u ⊕ u') |* B) ((v ⊕ v') |* D) (u |* B) (u' |* B) (v |* D) (v' |* D) (|*-distribʳ u u' B) (|*-distribʳ v v' D))

*-distribˡ : ∀ {s₁ s₂ s₃} → (x : Mat s₁ s₂) (y z : Mat s₂ s₃) → x * (y + z) m≈ x * y + x * z
*-distribˡ (Sing x) (Sing y) (Sing z) = Sing-eq (proj₁ R-distrib x y z)
*-distribˡ (Sing x) (RVec u) (RVec v) = RVec-eq (⊛|-distribˡ x u v)
*-distribˡ (RVec u) (CVec v) (CVec w) = Sing-eq (∙-distribˡ u v w)
*-distribˡ (RVec (two u v)) (quad A B C D) (quad A' B' C' D') = RVec-eq (two-eq (rearrangeLemma' {cm = cmv} (u |* (A + A')) (v |* (C + C')) (u |* A) (u |* A') (v |* C) (v |* C') (|*-distribˡ u A A') (|*-distribˡ v C C')) (rearrangeLemma' {cm = cmv} (u |* (B + B')) (v |* (D + D')) (u |* B) (u |* B') (v |* D) (v |* D') (|*-distribˡ u B B') (|*-distribˡ v D D')))
*-distribˡ (CVec v) (Sing x) (Sing y) = CVec-eq (|⊛-distribˡ v x y)
*-distribˡ (CVec (two u₁ v₁)) (RVec (two u₂ v₂)) (RVec (two u₃ v₃)) = quad-eq (⊛-distribˡ u₁ u₂ u₃) (⊛-distribˡ u₁ v₂ v₃) (⊛-distribˡ v₁ u₂ u₃) (⊛-distribˡ v₁ v₂ v₃)
*-distribˡ (quad A B C D) (CVec (two u v)) (CVec (two u' v')) = CVec-eq (two-eq (rearrangeLemma' {cm = cmv} (A *| (u ⊕ u')) (B *| (v ⊕ v')) (A *| u) (A *| u') (B *| v) (B *| v') (*|-distribˡ A u u') (*|-distribˡ B v v')) (rearrangeLemma' {cm = cmv} (C *| (u ⊕ u')) (D *| (v ⊕ v')) (C *| u) (C *| u') (D *| v) (D *| v') (*|-distribˡ C u u') (*|-distribˡ D v v')))
*-distribˡ (quad A₁ B₁ C₁ D₁) (quad A₂ B₂ C₂ D₂) (quad A₃ B₃ C₃ D₃) = quad-eq (rearrangeLemma' {cm = cmm} (A₁ * (A₂ + A₃)) (B₁ * (C₂ + C₃)) (A₁ * A₂) (A₁ * A₃) (B₁ * C₂) (B₁ * C₃) (*-distribˡ A₁ A₂ A₃) (*-distribˡ B₁ C₂ C₃)) (rearrangeLemma' {cm = cmm} (A₁ * (B₂ + B₃)) (B₁ * (D₂ + D₃)) (A₁ * B₂) (A₁ * B₃) (B₁ * D₂) (B₁ * D₃) (*-distribˡ A₁ B₂ B₃) (*-distribˡ B₁ D₂ D₃)) (rearrangeLemma' {cm = cmm} (C₁ * (A₂ + A₃)) (D₁ * (C₂ + C₃)) (C₁ * A₂) (C₁ * A₃) (D₁ * C₂) (D₁ * C₃) (*-distribˡ C₁ A₂ A₃) (*-distribˡ D₁ C₂ C₃)) (rearrangeLemma' {cm = cmm} (C₁ * (B₂ + B₃)) (D₁ * (D₂ + D₃)) (C₁ * B₂) (C₁ * B₃) (D₁ * D₂) (D₁ * D₃) (*-distribˡ C₁ B₂ B₃) (*-distribˡ D₁ D₂ D₃))

*-distribʳ : ∀ {s₁ s₂ s₃} → (x y : Mat s₁ s₂) (z : Mat s₂ s₃) → (x + y) * z m≈ x * z + y * z
*-distribʳ (Sing x) (Sing y) (Sing z) = Sing-eq (proj₂ R-distrib z x y)
*-distribʳ (Sing x) (Sing y) (RVec v) = RVec-eq (⊛|-distribʳ x y v)
*-distribʳ (RVec u) (RVec v) (CVec w) = Sing-eq (∙-distribʳ u v w)
*-distribʳ (RVec (two u v)) (RVec (two u' v')) (quad A B C D) = RVec-eq (two-eq (rearrangeLemma' {cm = cmv} ((u ⊕ u') |* A) ((v ⊕ v') |* C) (u |* A) (u' |* A) (v |* C) (v' |* C) (|*-distribʳ u u' A) (|*-distribʳ v v' C)) (rearrangeLemma' {cm = cmv} ((u ⊕ u') |* B) ((v ⊕ v') |* D) (u |* B) (u' |* B) (v |* D) (v' |* D) (|*-distribʳ u u' B) (|*-distribʳ v v' D)))
*-distribʳ (CVec u) (CVec v) (Sing x) = CVec-eq (|⊛-distribʳ u v x)
*-distribʳ (CVec (two u₁ v₁)) (CVec (two u₂ v₂)) (RVec (two u₃ v₃)) = quad-eq (⊛-distribʳ u₁ u₂ u₃) (⊛-distribʳ u₁ u₂ v₃) (⊛-distribʳ v₁ v₂ u₃) (⊛-distribʳ v₁ v₂ v₃)
*-distribʳ (quad A B C D) (quad A' B' C' D') (CVec (two u v)) = CVec-eq (two-eq (rearrangeLemma' {cm = cmv} ((A + A') *| u) ((B + B') *| v) (A *| u) (A' *| u) (B *| v) (B' *| v) (*|-distribʳ A A' u) (*|-distribʳ B B' v)) (rearrangeLemma' {cm = cmv} ((C + C') *| u) ((D + D') *| v) (C *| u) (C' *| u) (D *| v) (D' *| v) (*|-distribʳ C C' u) (*|-distribʳ D D' v)))
*-distribʳ (quad A₁ B₁ C₁ D₁) (quad A₂ B₂ C₂ D₂) (quad A₃ B₃ C₃ D₃) = quad-eq (rearrangeLemma' {cm = cmm} ((A₁ + A₂) * A₃) ((B₁ + B₂) * C₃) (A₁ * A₃) (A₂ * A₃) (B₁ * C₃) (B₂ * C₃) (*-distribʳ A₁ A₂ A₃) (*-distribʳ B₁ B₂ C₃)) (rearrangeLemma' {cm = cmm} ((A₁ + A₂) * B₃) ((B₁ + B₂) * D₃) (A₁ * B₃) (A₂ * B₃) (B₁ * D₃) (B₂ * D₃) (*-distribʳ A₁ A₂ B₃) (*-distribʳ B₁ B₂ D₃)) (rearrangeLemma' {cm = cmm} ((C₁ + C₂) * A₃) ((D₁ + D₂) * C₃) (C₁ * A₃) (C₂ * A₃) (D₁ * C₃) (D₂ * C₃) (*-distribʳ C₁ C₂ A₃) (*-distribʳ D₁ D₂ C₃)) (rearrangeLemma' {cm = cmm} ((C₁ + C₂) * B₃) ((D₁ + D₂) * D₃) (C₁ * B₃) (C₂ * B₃) (D₁ * D₃) (D₂ * D₃) (*-distribʳ C₁ C₂ B₃) (*-distribʳ D₁ D₂ D₃))

◂|-distribˡ : ∀ {s} → (x : Tri s) (u v : Vec s) → x ◂| (u ⊕ v) v≈ x ◂| u ⊕ x ◂| v
◂|-distribˡ one (one x) (one x') = one-eq (≈sym (proj₁ R+-identity R0)) --symV (proj₁ {!R+-identity!})
◂|-distribˡ (two U R L) (two u₁ v₁) (two u₂ v₂) = two-eq (rearrangeLemma' {cm = cmv} (U ◂| (u₁ ⊕ u₂)) (R *| (v₁ ⊕ v₂)) (U ◂| u₁) (U ◂| u₂) (R *| v₁) (R *| v₂) (◂|-distribˡ U u₁ u₂) (*|-distribˡ R v₁ v₂)) (◂|-distribˡ L v₁ v₂)


◂|-distribʳ : ∀ {s} → (x y : Tri s) (v : Vec s) → (x ◂+ y) ◂| v v≈ x ◂| v ⊕ y ◂| v
◂|-distribʳ one u v = one-eq (≈sym (proj₁ R+-identity R0))
◂|-distribʳ (two U R L) (two U' R' L') (two u v) = two-eq (rearrangeLemma' {cm = cmv} ((U ◂+ U') ◂| u) ((R + R') *| v) (U ◂| u) (U' ◂| u) (R *| v) (R' *| v) (◂|-distribʳ U U' u) (*|-distribʳ R R' v)) (◂|-distribʳ L L' v)

|◂-distribˡ : ∀ {s} → (v : Vec s) (x y : Tri s) → v |◂ (x ◂+ y) v≈ v |◂ x ⊕ v |◂ y
|◂-distribˡ (one x) u v = one-eq (≈sym (proj₁ R+-identity R0))
|◂-distribˡ (two u v) (two U R L) (two U' R' L') = two-eq (|◂-distribˡ u U U') (rearrangeLemma' {cm = cmv} (u |* (R + R')) (v |◂ (L ◂+ L')) (u |* R) (u |* R') (v |◂ L) (v |◂ L') (|*-distribˡ u R R') (|◂-distribˡ v L L'))

|◂-distribʳ : ∀ {s} → (u v : Vec s) (x : Tri s) → (u ⊕ v) |◂ x v≈ u |◂ x ⊕ v |◂ x
|◂-distribʳ (one x) (one y) one = one-eq (≈sym (proj₁ R+-identity R0))
|◂-distribʳ (two u v) (two u' v') (two U R L) = two-eq (|◂-distribʳ u u' U) (rearrangeLemma' {cm = cmv} ((u ⊕ u') |* R) ((v ⊕ v') |◂ L) (u |* R) (u' |* R) (v |◂ L) (v' |◂ L) (|*-distribʳ u u' R) (|◂-distribʳ v v' L))
◂*-distribˡ : ∀ {s₁ s₂} → (x : Tri s₁) (y z : Mat s₁ s₂) → x ◂* (y + z) m≈ (x ◂* y + x ◂* z)
◂*-distribˡ one (Sing _) (Sing _) = Sing-eq (≈sym (proj₁ R+-identity R0))
◂*-distribˡ one (RVec _) (RVec _) = RVec-eq (two-eq (symV (identityˡV zeroVec)) (symV (identityˡV zeroVec)))
◂*-distribˡ (two U R L) (CVec u) (CVec v) = CVec-eq (◂|-distribˡ (two U R L) u v)
◂*-distribˡ (two U R L) (quad A B C D) (quad A' B' C' D') = quad-eq (rearrangeLemma' {cm = cmm} (U ◂* (A + A')) (R * (C + C')) (U ◂* A) (U ◂* A') (R * C) (R * C') (◂*-distribˡ U A A') (*-distribˡ R C C')) (rearrangeLemma' {cm = cmm} (U ◂* (B + B')) (R * (D + D')) (U ◂* B) (U ◂* B') (R * D) (R * D') (◂*-distribˡ U B B') (*-distribˡ R D D')) (◂*-distribˡ L C C') (◂*-distribˡ L D D')

◂*-distribʳ : ∀ {s₁ s₂} → (x y : Tri s₁) (z : Mat s₁ s₂) → (x ◂+ y) ◂* z m≈ x ◂* z + y ◂* z
◂*-distribʳ one one (Sing x) = Sing-eq (≈sym (proj₁ R+-identity R0))
◂*-distribʳ one one (RVec y) = RVec-eq (two-eq (symV (identityˡV zeroVec)) (symV (identityˡV zeroVec)))
◂*-distribʳ (two U R L) (two U' R' L') (CVec (two u v)) = CVec-eq (two-eq (rearrangeLemma' {cm = cmv} ((U ◂+ U') ◂| u) ((R + R') *| v) (U ◂| u) (U' ◂| u) (R *| v) (R' *| v) (◂|-distribʳ U U' u) (*|-distribʳ R R' v)) (◂|-distribʳ L L' v))
◂*-distribʳ (two U R L) (two U' R' L') (quad A B C D) = quad-eq (rearrangeLemma' {cm = cmm} ((U ◂+ U') ◂* A) ((R + R') * C) (U ◂* A) (U' ◂* A) (R * C) (R' * C) (◂*-distribʳ U U' A) (*-distribʳ R R' C)) (rearrangeLemma' {cm = cmm} ((U ◂+ U') ◂* B) ((R + R') * D) (U ◂* B) (U' ◂* B) (R * D) (R' * D) (◂*-distribʳ U U' B) (*-distribʳ R R' D)) (◂*-distribʳ L L' C) (◂*-distribʳ L L' D)



-- distributivity for *◂
*◂-distribˡ : ∀ {s₁ s₂} → (x : Mat s₁ s₂) (y z : Tri s₂) → x *◂ (y ◂+ z) m≈ (x *◂ y + x *◂ z)
*◂-distribˡ (Sing x) one one = Sing-eq (≈sym (proj₁ R+-identity R0))
*◂-distribˡ (RVec v) x y = RVec-eq (|◂-distribˡ v x y)
*◂-distribˡ (CVec v) one one = CVec-eq (two-eq (symV (identityˡV zeroVec)) (symV (identityˡV zeroVec)))
*◂-distribˡ (quad A B C D) (two U R L) (two U' R' L') = quad-eq (*◂-distribˡ A U U') (rearrangeLemma' {cm = cmm} (A * (R + R')) (B *◂ (L ◂+ L')) (A * R) (A * R') (B *◂ L) (B *◂ L') (*-distribˡ A R R') (*◂-distribˡ B L L')) (*◂-distribˡ C U U') (rearrangeLemma' {cm = cmm} (C * (R + R')) (D *◂ (L ◂+ L')) (C * R) (C * R') (D *◂ L) (D *◂ L') (*-distribˡ C R R') (*◂-distribˡ D L L')) 

*◂-distribʳ : ∀ {s₁ s₂} → (x y : Mat s₁ s₂) (z : Tri s₂) → (x + y) *◂ z m≈ x *◂ z + y *◂ z
*◂-distribʳ (Sing x) (Sing y) one = Sing-eq (≈sym (proj₁ R+-identity R0))
*◂-distribʳ (RVec (two u v)) (RVec (two u' v')) (two U R L) = RVec-eq (two-eq (|◂-distribʳ u u' U) (rearrangeLemma' {cm = cmv} ((u ⊕ u') |* R) ((v ⊕ v') |◂ L) (u |* R) (u' |* R) (v |◂ L) (v' |◂ L) (|*-distribʳ u u' R) (|◂-distribʳ v v' L)))
*◂-distribʳ (CVec v) (CVec v') one = CVec-eq (two-eq (symV (identityˡV zeroVec)) (symV (identityˡV zeroVec)))
*◂-distribʳ (quad A B C D) (quad A' B' C' D') (two U R L) = quad-eq (*◂-distribʳ A A' U) (rearrangeLemma' {cm = cmm} ((A + A') * R) ((B + B') *◂ L) (A * R) (A' * R) (B *◂ L) (B' *◂ L) (*-distribʳ A A' R) (*◂-distribʳ B B' L)) (*◂-distribʳ C C' U) (rearrangeLemma' {cm = cmm} ((C + C') * R) ((D + D') *◂ L) (C * R) (C' * R) (D *◂ L) (D' *◂ L) (*-distribʳ C C' R) (*◂-distribʳ D D' L))
--*◂-distrib : 




◂-distribˡ : ∀ {s} → (x y z : Tri s) → x ◂ (y ◂+ z) t≈ x ◂ y ◂+ x ◂ z -- (U₁ ◂* R₂ + U₁ ◂* R₃) + (R₁ *◂ L₂ + R₁ *◂ L₃) m≈
◂-distribˡ one one one = one-eq
◂-distribˡ (two U₁ R₁ L₁) (two U₂ R₂ L₂) (two U₃ R₃ L₃) = two-eq (◂-distribˡ U₁ U₂ U₃) (rearrangeLemma' {cm = cmm} (U₁ ◂* (R₂ + R₃)) (R₁ *◂ (L₂ ◂+ L₃)) (U₁ ◂* R₂) (U₁ ◂* R₃) (R₁ *◂ L₂) (R₁ *◂ L₃) (◂*-distribˡ U₁ R₂ R₃) (*◂-distribˡ R₁ L₂ L₃)) --(lemma U₁ R₁ R₂ R₃ L₂ L₃) 
                                                                                     (◂-distribˡ L₁ L₂ L₃)

◂-distribʳ : ∀ {s} → (x y z : Tri s) → (y ◂+ z) ◂ x t≈ y ◂ x ◂+ z ◂ x
◂-distribʳ one one one = one-eq
◂-distribʳ (two U₁ R₁ L₁) (two U₂ R₂ L₂) (two U₃ R₃ L₃) = two-eq (◂-distribʳ U₁ U₂ U₃) (rearrangeLemma' {cm = cmm} ((U₂ ◂+ U₃) ◂* R₁) ((R₂ + R₃) *◂ L₁) (U₂ ◂* R₁) (U₃ ◂* R₁) (R₂ *◂ L₁) (R₃ *◂ L₁) (◂*-distribʳ U₂ U₃ R₁) (*◂-distribʳ R₂ R₃ L₁)) 
                                                                 (◂-distribʳ L₁ L₂ L₃)

◂-distrib : ∀ {s} → _DistributesOver_ (_t≈_ {s}) _◂_ _◂+_
◂-distrib = ◂-distribˡ , ◂-distribʳ