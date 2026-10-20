/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.Basic

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- The canonical additive subgroup of cycles of degree `k`, retained as a typed
compatibility bridge for imports of this module. -/
#check (AlgebraicGeometry.AlgebraicSpace.Hom.cycleGroup :
  ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S} (f : X ⟶ B) [LocallyOfFiniteType f]
    (δ : Points B → ℤ) (k : ℤ),
    AddSubgroup (Function.locallyFinsupp (Points X) ℤ))
