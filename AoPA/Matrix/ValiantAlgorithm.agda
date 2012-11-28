open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Product
open import Data.Sum

import Matrix.Abstract
import Matrix.NewNewSplit
open import Matrix.STree

open import Matrix.NonAssociativeNonRing

open import Level using () renaming (zero to Lzero)

module ValiantAlgorithm (NAR : NonAssociativeNonRing Lzero Lzero) where