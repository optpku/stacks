/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Differentials.Transitivity

/-! The canonical transitivity sequence of relative differentials is right exact. -/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Hom.Differentials.Transitivity.exact_and_epi :
  ∀ {S : Scheme.{u}} {X Y B : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ B),
    (Hom.Differentials.Transitivity.complex f g).Exact ∧
      Epi (Hom.Differentials.Transitivity.projection f g))
