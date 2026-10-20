/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.ValuativeCriterion

open CategoryTheory AlgebraicGeometry

universe u

/- The existence part of the valuative criterion for lifted groupoid fibrations. -/
#check (AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.ValuativeCriterion.Existence :
  {S : Scheme.{u}} →
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)} →
      (X ⟶ Y) → Prop)
