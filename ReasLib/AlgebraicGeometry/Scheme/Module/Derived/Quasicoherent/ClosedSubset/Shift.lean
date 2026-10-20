module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.ClosedSubset
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Structure

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh.SupportedOn

/-- Derived quasi-coherent modules supported on a closed subset are stable under shifts. -/
instance instIsStableUnderShift (X : Scheme.{u}) (T : TopologicalSpace.Closeds X) :
    (quasiCoherentOnSupport X T).IsStableUnderShift ℤ := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh.SupportedOn
