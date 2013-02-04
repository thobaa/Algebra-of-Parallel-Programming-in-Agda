-- here we put mathematical operations for Triangles

-- TODO
-- add stuff

--Own
open import Valiant.Abstract.NonAssociativeNonRing using (NonAssociativeNonRing)
import Valiant.Abstract.Triangle as Triangle using ()

module Valiant.Abstract.Triangle.Operations {l₁ l₂} (NAR : NonAssociativeNonRing l₁ l₂) where

open Triangle NAR