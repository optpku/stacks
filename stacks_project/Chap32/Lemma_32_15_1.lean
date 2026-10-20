/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.ValuativeCriterion.Noetherian

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 32.15.1: for a finite-type morphism `f : X ⟶ Y` with `Y` locally Noetherian,
every point in the closure of the image is the closed-point image of a valuative square based at
a generic point of `X`, with valuation subring either a discrete valuation ring or a field. -/
@[stacks 0CM2]
#check
  (AlgebraicGeometry.Scheme.Hom.exists_dvrOrFieldValuativeCommSqAt_of_mem_closure_range :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [Scheme.Hom.FiniteType f]
      [IsLocallyNoetherian Y] {y : Y},
      y ∈ closure (Set.range f.base) →
        ∃ sq : AlgebraicGeometry.DvrOrFieldValuativeCommSqAt f,
          sq.closedPointImage = y)
