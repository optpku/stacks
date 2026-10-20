/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup
public import ReasLib.AlgebraicGeometry.Scheme.Module.FilteredK0

/-!
# Chow groups and the coherent support filtration

This file constructs the canonical map from a Chow group to the Grothendieck group of a
two-step interval in the coherent support filtration.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup

open Scheme.Modules

variable {S X : Scheme.{u}} (f : X ⟶ S) [UniversallyCatenary S]
  [LocallyOfFiniteType f] (δ : S → ℤ) [IsDimensionFunction δ] (k : ℤ)

/-- Rational-equivalence boundaries lie in the kernel of the cycle map to
`K₀(Coh≤k+1(X) / Coh≤k-1(X))`. -/
theorem rationalBoundaries_le_toFilteredK0_ker :
    @RationalEquivalence.boundaries X (LocallyOfFiniteType.isLocallyNoetherian f)
        (f.relativeDimensionFunction δ) inferInstance k ≤
      (CycleGroup.toFilteredK0 f δ k).ker := sorry

/-- The canonical map from `CH_k(X)` to `K₀(Coh≤k+1(X) / Coh≤k-1(X))`. -/
noncomputable def toFilteredK0 :
    @AlgebraicGeometry.ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian f)
        (f.relativeDimensionFunction δ) inferInstance k →+
      FilteredK0 f δ (k + 1) (k - 1) :=
  QuotientAddGroup.lift
    (@RationalEquivalence.boundaries X (LocallyOfFiniteType.isLocallyNoetherian f)
      (f.relativeDimensionFunction δ) inferInstance k)
    (CycleGroup.toFilteredK0 f δ k)
    (rationalBoundaries_le_toFilteredK0_ker f δ k)

/-- The Chow-group map is induced by the cycle-to-graded-`K₀` map followed by transition to
the wider filtered quotient. -/
theorem toFilteredK0_comp_chowClass :
    (toFilteredK0 f δ k).comp
        (@chowClass X (LocallyOfFiniteType.isLocallyNoetherian f)
          (f.relativeDimensionFunction δ) inferInstance k) =
      (GradedK0.toFilteredK0 f δ k).comp (GradedK0.toK0 f δ k) := sorry

end AlgebraicGeometry.ChowGroup
