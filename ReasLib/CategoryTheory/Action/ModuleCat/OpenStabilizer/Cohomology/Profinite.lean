/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Action.ModuleCat.OpenStabilizer.Cohomology
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
public import Mathlib.Algebra.Module.Torsion.Basic

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Action.ModuleCat.DiscreteModuleCat

/-- Positive-degree continuous cohomology of a discrete module over a profinite group is torsion. -/
theorem profiniteGroupCohomology_isTorsion
    (G : ProfiniteGrp) (M : DiscreteModuleCat ℤ G)
    (i : ℕ) (hi : 0 < i) :
    Module.IsTorsion ℤ ((cohomologyFunctor ℤ G i).obj M) := sorry

/-- Positive-degree continuous cohomology vanishes for discrete rational vector-space coefficients. -/
theorem profiniteGroupCohomology_isZero_of_rationalVector
    (G : ProfiniteGrp) (M : DiscreteModuleCat ℚ G)
    (i : ℕ) (hi : 0 < i) :
    IsZero ((cohomologyFunctor ℤ G i).obj
      ((restrictScalars (Int.castRingHom ℚ)).obj M)) := sorry

end CategoryTheory.Action.ModuleCat.DiscreteModuleCat
