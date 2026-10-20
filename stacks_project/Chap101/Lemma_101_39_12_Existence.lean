/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.ValuativeCriterion

open CategoryTheory AlgebraicGeometry

universe u

#check (AlgebraicGeometry.AlgebraicStack.ValuativeCriterion.Existence :
  {S : Scheme.{u}} → {X Y : GroupoidsOver S} →
    [AlgebraicGeometry.AlgebraicStack X] → [AlgebraicGeometry.AlgebraicStack Y] →
    (X ⟶ Y) → Prop)
