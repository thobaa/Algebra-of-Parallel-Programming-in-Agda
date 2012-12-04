open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Product
open import Data.Sum

import Matrix.Abstract
import Matrix.NewNewSplit
open import Matrix.STree

open import Matrix.NonAssociativeNonRing

open import Level using () renaming (zero to Lzero)

import Matrix.NewNewSplit
import Matrix.Tri

module ValiantAlgorithm (NAR : NonAssociativeNonRing Lzero Lzero) where

open Matrix.NewNewSplit (NAR)
open Matrix.Tri (NAR)

-- the algorithm is a map!
-- tar en tri till 

-- intermediate structure:
--divide : ∀ {s} → Tri s → SplitMat  × SplitMat × SplitMat × SplitMat × SplitMat × SplitMat
--divide = ?
--data interMediate : Set where
  

-- takes a matrix to a thing with substructures:
