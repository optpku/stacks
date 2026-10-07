module

public import ReasLib.AlgebraicGeometry.ChowCohomology

open AlgebraicGeometry CategoryTheory

universe u

#check (AlgebraicGeometry.ChowCohomology.ring :
  ∀ {S X : Scheme.{u}} (delta : S → ℤ) (p : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction delta] [LocallyOfFiniteType p],
    Type (u + 1))
