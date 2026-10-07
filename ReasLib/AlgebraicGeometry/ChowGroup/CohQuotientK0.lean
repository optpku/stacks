module

public import ReasLib.AlgebraicGeometry.ChowGroup.FilteredK0
public import ReasLib.AlgebraicGeometry.Scheme.Module.CohQuotientK0

/-!
# Chow groups and full coherent Serre quotients

This file constructs the canonical map from a Chow group to the Grothendieck group of
coherent sheaves modulo a support bound.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup

open Scheme.Modules

variable {S X : Scheme.{u}} (f : X ⟶ S) [UniversallyCatenary S]
  [LocallyOfFiniteType f] (δ : S → ℤ) [IsDimensionFunction δ] (k : ℤ)

/-- The canonical map from `CH_k(X)` to `K₀(Coh(X) / Coh≤k-1(X))`. -/
noncomputable def toCohQuotientK0 :
    @AlgebraicGeometry.ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian f)
        (f.relativeDimensionFunction δ) inferInstance k →+
      CohQuotientK0 f δ (k - 1) :=
  (FilteredK0.toCohQuotient f δ (k + 1) (k - 1)).comp
    (toFilteredK0 f δ k)

/-- The canonical Chow-group map is the composite of the filtered map and the
bounded-to-full quotient transition. -/
theorem toCohQuotientK0_def :
    toCohQuotientK0 f δ k =
      (FilteredK0.toCohQuotient f δ (k + 1) (k - 1)).comp
        (toFilteredK0 f δ k) := sorry

end AlgebraicGeometry.ChowGroup
