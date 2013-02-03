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

module Matrix.Overlap (NAR : NonAssociativeNonRing Lzero Lzero) where

open Matrix.Abstract (NAR) using ()
open Matrix.Tri (NAR)      using (Tri; _T+_; _T*_; valiantOverlap'; foldTri; one; two; tri1; rec; tri2)
open Matrix.NewNewSplit (NAR) using (splitSize; SplitMat)
open Matrix.TriFold (NAR)

-- specification of the overlap, using my idea (though JP began implementing, while we were talking, a while ago)

-- multiply size of left 
overlap-sum : {!!}
overlap-sum = {!!}

overlap-spec : {!!}
overlap-spec = {!!}