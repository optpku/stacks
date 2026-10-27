/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.Transitivity.Splitting

/-!
# Compatibility bridge for conormal transitivity

The reusable conormal transitivity API is owned by `ReasLib`; this source-side
file preserves the typed compatibility check used by existing chapter callers.
-/

open CategoryTheory AlgebraicGeometry

universe u

#check
  (AlgebraicGeometry.AlgebraicSpace.Hom.Conormal.Transitivity.exact_and_epi :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
      (i : Z ⟶ Y) (j : Y ⟶ X) [AlgebraicGeometry.AlgebraicSpace.IsImmersion i]
      [AlgebraicGeometry.AlgebraicSpace.IsImmersion j],
      (AlgebraicGeometry.AlgebraicSpace.Hom.Conormal.Transitivity.complex i j).Exact ∧
        Epi (AlgebraicGeometry.AlgebraicSpace.Hom.Conormal.Transitivity.projection i j))
