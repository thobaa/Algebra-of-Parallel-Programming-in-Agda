open import Valiant.Abstract.NonAssociativeNonRing
open import Valiant.Abstract.NonAssociativeNonRing.Structure
module ImportAll {l₁ l₂} (NAR : NonAssociativeNonRing l₁ l₂) where


import Valiant.Abstract.Matrix
import Valiant.Abstract.Triangle
import Valiant.Abstract.Matrix.Operations
import Valiant.Abstract.Triangle.Operations
import Valiant.Abstract.Proofs -- not used yet
import Valiant.Concrete.Tri
import Valiant.Concrete.Tri.Operations
import Valiant.Concrete.Mat
import Valiant.Concrete.Mat.Operations
import Valiant.Concrete.Splitting
-- representation and matrixalgebra not incluede yet
--import Valiant.Specs.JPSpec
import Valiant.Helper.Definitions
import Valiant.Algorithm.Algorithm
open Valiant.Abstract.Matrix NAR
open Valiant.Abstract.Triangle NAR 
open Valiant.Abstract.Matrix.Operations NAR
open Valiant.Abstract.Triangle.Operations NAR
open Valiant.Abstract.Proofs
open Valiant.Concrete.Tri NAR
open Valiant.Concrete.Tri.Operations NAR
open Valiant.Concrete.Mat NAR
open Valiant.Concrete.Mat.Operations NAR
open Valiant.Concrete.Splitting
open Valiant.Helper.Definitions NAR
open Valiant.Algorithm.Algorithm NAR
--open Valiant.Specs.JPSpec NAR