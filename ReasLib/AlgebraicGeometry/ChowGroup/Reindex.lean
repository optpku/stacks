module

public import ReasLib.AlgebraicGeometry.ChowGroup

/-!
# Reindexing Chow groups

This file transports Chow classes between equal grading indices.
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup

/-- Transport a Chow group along an equality of grading indices. -/
noncomputable def reindex {X : Scheme.{u}} [IsLocallyNoetherian X]
    (d : X → ℤ) [IsDimensionFunction d] {a b : ℤ} (h : a = b) :
    ChowGroup X d a ≃+ ChowGroup X d b :=
  AddEquiv.cast (M := fun n : ℤ ↦ ChowGroup X d n) h

/-- Transporting a Chow group along reflexivity is the identity additive equivalence. -/
theorem reindex_refl {X : Scheme.{u}} [IsLocallyNoetherian X]
    (d : X → ℤ) [IsDimensionFunction d] (a : ℤ) :
    reindex d (rfl : a = a) = AddEquiv.refl (ChowGroup X d a) := sorry

end AlgebraicGeometry.ChowGroup
