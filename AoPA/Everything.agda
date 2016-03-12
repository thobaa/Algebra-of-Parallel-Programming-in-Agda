module AoPA.Everything where


-- Basic definitions.

import AoPA.Sets

import AoPA.Relations
import AoPA.Relations.Function
import AoPA.Relations.PowerTrans
import AoPA.Relations.Product
import AoPA.Relations.Coreflexive
import AoPA.Relations.Factor
import AoPA.Relations.Converse
import AoPA.Relations.CompChain
import AoPA.Relations.Minimum
import AoPA.Relations.WellFound

-- Algebraic reasoning

import AoPA.AlgebraicReasoning.MonoPreorderReasoning
import AoPA.AlgebraicReasoning.PolyPreorderReasoning
import AoPA.AlgebraicReasoning.PolyPreorderReasoning1
import AoPA.AlgebraicReasoning.PipeReasoning
import AoPA.AlgebraicReasoning.Equality
import AoPA.AlgebraicReasoning.ExtensionalEquality
import AoPA.AlgebraicReasoning.Sets
import AoPA.AlgebraicReasoning.Relations
import AoPA.AlgebraicReasoning.Implications

-- Datatypes and their folds

import AoPA.Data.List.Fold
import AoPA.Data.List.Unfold
import AoPA.Data.List.ConvFunThm
import AoPA.Data.List.GreedyThm
import AoPA.Data.List.HyloThm
import AoPA.Data.List.Utilities
{- To be updated 
import Data.Tree
import Data.Tree.Fold
import Data.Tree.Unfold
-}

-- Examples

-- import Examples.MSS.IntRNG   -- not finished yet!
import AoPA.Examples.MSS.List+
import AoPA.Examples.MSS.ListProperties
import AoPA.Examples.MSS.Derivation
-- import Examples.MSS.MSS      -- unfinished because IntRNG is not.

import AoPA.Examples.Sorting.Bags
import AoPA.Examples.Sorting.Spec
import AoPA.Examples.Sorting.iSort

{- To be updated
import Examples.Optimisation.ActivitySelection
import Examples.Sorting.qSort
-}
