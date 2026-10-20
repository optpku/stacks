/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.Cutoff.Basic

/-! Typed compatibility entry for the integer-degree homogeneous cutoff carrier. -/

open CategoryTheory AlgebraicGeometry

universe u

section

variable {S : Scheme.{u}} [UniversallyCatenary S]
  (δ : S → ℤ) [IsDimensionFunction δ]
  {Z X : Over S} [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType X.hom]
  (f : Z ⟶ X) [IsClosedImmersion f.left]

#check (AlgebraicGeometry.BivariantClass.Cutoff δ f : ℕ → ℤ → Type (u + 1))

end
