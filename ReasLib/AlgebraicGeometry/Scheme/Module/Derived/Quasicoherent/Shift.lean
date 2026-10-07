module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.CohomologyIn
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Structure

/-!
# Shifts of Derived Modules with Quasicoherent Cohomology

The canonical shifts on the ambient derived category restrict to the full subcategory of
derived modules whose cohomology sheaves are quasicoherent.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- The canonical shifts on derived modules restrict to derived modules with quasicoherent
cohomology. -/
noncomputable instance derivedQCohHasShift (X : Scheme.{u}) :
    HasShift (Scheme.ModuleDerived.Quasicoherent X) ℤ :=
  ObjectProperty.hasShift (Scheme.ModuleDerived.quasicoherentProperty X)

end AlgebraicGeometry.Scheme.DerivedQCoh
