/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Weighting

@[expose] public section

open CategoryTheory

universe u

/- Lemma 37.75.5: the pointwise product of weightings of two locally quasi-finite
morphisms is a weighting of their composite. -/
@[stacks 0GK9] #check
  (AlgebraicGeometry.Scheme.Hom.IsWeighting.comp :
    ∀ {X Y Z : AlgebraicGeometry.Scheme.{u}}
      {f : X ⟶ Y} {g : Y ⟶ Z}
      [AlgebraicGeometry.LocallyQuasiFinite f]
      [AlgebraicGeometry.LocallyQuasiFinite g]
      {w_f : X → ℤ} {w_g : Y → ℤ},
      f.IsWeighting w_f → g.IsWeighting w_g →
        (f ≫ g).IsWeighting (fun x ↦ w_f x * w_g (f x)))
