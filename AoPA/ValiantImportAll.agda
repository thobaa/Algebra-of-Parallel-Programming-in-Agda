open import Valiant.Abstract.NonAssociativeNonRing
open import Valiant.Abstract.NonAssociativeNonRing.Structure
module ValiantImportAll {l₁ l₂} (NAR : NonAssociativeNonRing l₁ l₂) where

-- importing stuff

-- Abstract (excluding NANR, NANR.Structure)
import Valiant.Abstract.Matrix

import Valiant.Abstract.Triangle

import Valiant.Abstract.Matrix.Operations
import Valiant.Abstract.Triangle.Operations
import Valiant.Abstract.Matrix.NANRing
import Valiant.Abstract.Triangle.NANRing

--import Valiant.Abstract.Proofs -- empty

-- Algorithm
import Valiant.Algorithm.Algorithm

-- Concrete
import Valiant.Concrete.Mat
import Valiant.Concrete.Splitting
import Valiant.Concrete.Tri 
import Valiant.Concrete.Mat.Operations
import Valiant.Concrete.Mat.Properties
import Valiant.Concrete.Tri.CommutativeMonoid
import Valiant.Concrete.Tri.Congruences
import Valiant.Concrete.Tri.Distributivities
import Valiant.Concrete.Tri.Equalities
import Valiant.Concrete.Tri.Operations
import Valiant.Concrete.Tri.Properties
import Valiant.Concrete.Tri.Zeros
{-
-- Helper
import Valiant.Helper.Definitions

-- MatrixAlgebra (should be removed)
import Valiant.MatrixAlgebra.Definitions
import Valiant.MatrixAlgebra.Matrix
import Valiant.MatrixAlgebra.NatLemmas
import Valiant.MatrixAlgebra.UTriang
import Valiant.MatrixAlgebra.VecLemmas
import Valiant.MatrixAlgebra.ZLemmas

-- Representation (not much content)
import Valiant.Representation.MatRep
import Valiant.Representation.MatRepProofs
import Valiant.Representation.TriRep

-- Specs
import Valiant.Specs.JPSpec
import Valiant.Specs.Overlap


----------------------------------------------------------------------

-- opening stuff
-- Abstract (including NANR, NANR.Structure)
open Valiant.Abstract.Matrix NAR
open Valiant.Abstract.Triangle NAR
open Valiant.Abstract.Matrix.Operations NAR
open Valiant.Abstract.Triangle.Operations NAR
open Valiant.Abstract.Matrix.NANRing NAR
open Valiant.Abstract.Triangle.NANRing NAR
--open Valiant.Abstract.Proofs NAR -- empty

-- Algorithm
open Valiant.Algorithm.Algorithm NAR

-- Concrete
open Valiant.Concrete.Mat NAR
open Valiant.Concrete.Splitting -- Not parametrized
open Valiant.Concrete.Tri NAR
open Valiant.Concrete.Mat.Operations NAR
open Valiant.Concrete.Mat.Properties
open Valiant.Concrete.Tri.CommutativeMonoid NAR
open Valiant.Concrete.Tri.Congruences NAR
open Valiant.Concrete.Tri.Distributivities NAR
open Valiant.Concrete.Tri.Equalities NAR
open Valiant.Concrete.Tri.Operations NAR
open Valiant.Concrete.Tri.Properties NAR
open Valiant.Concrete.Tri.Zeros NAR

-- Helper
open Valiant.Helper.Definitions NAR

-- MatrixAlgebra (should be removed), NOT PARAMETRIZED
open Valiant.MatrixAlgebra.Definitions
open Valiant.MatrixAlgebra.Matrix
open Valiant.MatrixAlgebra.NatLemmas
open Valiant.MatrixAlgebra.UTriang
open Valiant.MatrixAlgebra.VecLemmas
open Valiant.MatrixAlgebra.ZLemmas

-- Representation (not much content)
open Valiant.Representation.MatRep NAR
open Valiant.Representation.MatRepProofs NAR
open Valiant.Representation.TriRep NAR

-- Specs
open Valiant.Specs.JPSpec NAR
open Valiant.Specs.Overlap NAR

-}
