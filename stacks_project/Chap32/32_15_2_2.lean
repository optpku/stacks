/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.ValuativeCriterion.Diagonal
import StacksCheckRecall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

universe u

/- 32.15.2.2: for a chosen lift of the valuative square of the diagonal
`X₀ ⟶ X₀ ×[S] X₀`, the bottom morphism followed by the first pullback projection
is the dotted lifting morphism. -/
@[stacks 05M1] #check
  (AlgebraicGeometry.ValuativeCommSq.diagonalLift_comp_fst :
    {X₀ S : Scheme.{u}} → {f : X₀ ⟶ S} →
      (sq : ValuativeCommSq (pullback.diagonal f)) → (l : sq.commSq.LiftStruct) →
        sq.i₂ ≫ pullback.fst f f = l.l)

/- For the same chosen lift, the bottom morphism followed by the second pullback projection
is the dotted lifting morphism. -/
#check
  (AlgebraicGeometry.ValuativeCommSq.diagonalLift_comp_snd :
    {X₀ S : Scheme.{u}} → {f : X₀ ⟶ S} →
      (sq : ValuativeCommSq (pullback.diagonal f)) → (l : sq.commSq.LiftStruct) →
        sq.i₂ ≫ pullback.snd f f = l.l)
