/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.FilteredK0
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedCycle.TwoPeriodic

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme.Modules.GradedK0

variable {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S]
  [LocallyOfFiniteType p] (δ : S → ℤ) [IsDimensionFunction δ] (k : ℤ)

/-- The image of the canonical transition from the degree-`k` graded Grothendieck group
to the filtered Grothendieck group. -/
noncomputable def filteredImage :
    AddSubgroup (FilteredK0 p δ (k + 1) (k - 1)) :=
  (toFilteredK0 p δ k).range

/-- A filtered Grothendieck class belongs to `filteredImage p δ k` exactly when it is
the image of a degree-`k` graded Grothendieck class. -/
theorem mem_filteredImage_iff
    (z : FilteredK0 p δ (k + 1) (k - 1)) :
    z ∈ filteredImage p δ k ↔
      ∃ y : GradedK0 p δ k, toFilteredK0 p δ k y = z := sorry

end Scheme.Modules.GradedK0

namespace ChowGroup

open Scheme.Modules

variable {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S]
  [LocallyOfFiniteType p] (δ : S → ℤ) [IsDimensionFunction δ] (k : ℤ)

/-- The canonical map from the degree-`k` Chow group to
`K₀(Coh≤k+1(X) / Coh≤k-1(X))` is bijective onto the image of the transition from
`K₀(Coh≤k(X) / Coh≤k-1(X))`. -/
theorem toFilteredK0_bijOn :
    Set.BijOn (toFilteredK0 p δ k) Set.univ
      (GradedK0.filteredImage p δ k) := sorry

end ChowGroup
end AlgebraicGeometry
