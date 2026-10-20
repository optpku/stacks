/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.Noetherian

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

-- Source context: The authorized correction allows a field for trivial specializations,
-- retaining the source's residue-field and codimension-zero requirements.
/- Lemma 70.21.1: A point in the closure of the image of a finite-type morphism to a locally
Noetherian algebraic space is reached by a DVR-or-field valuative square. -/
@[stacks 0CMC] #check
  (AlgebraicGeometry.AlgebraicSpace.exists_dvrOrFieldValuativeCommSqAt_of_mem_closure_range :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [FiniteType f] [IsLocallyNoetherian Y]
      {y : Points Y} {τ : TopologicalSpace (Points Y)}
      (hτ : IsPointsTopology Y τ)
      (hy : y ∈ @closure (Points Y) τ (Set.range (Points.map f))),
      ∃ sq : DvrOrFieldValuativeCommSqAt f, sq.closedPointImage = y)
