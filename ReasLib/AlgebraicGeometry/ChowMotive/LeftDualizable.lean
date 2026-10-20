/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowMotive
public import ReasLib.AlgebraicGeometry.Correspondence.GradedCategory
public import ReasLib.CategoryTheory.Monoidal.Duality.Dualizable
public import ReasLib.CategoryTheory.Idempotents.Karoubi.Monoidal

@[expose] public section

universe u

namespace ChowMotive

/-- Every object of the category of rational Chow motives over a field admits a left dual. -/
theorem isLeftDualizable {k : Type u} [Field k]
    (M : ChowMotive k (fun _ ↦ AlgebraicGeometry.Correspondence.GradedCategory k)) :
    CategoryTheory.IsLeftDualizable M := sorry

end ChowMotive
