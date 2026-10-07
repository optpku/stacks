module

public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Theory
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.RankDecomposition

@[expose] public section

open CategoryTheory

universe u

/- The operational Chern-class theory is provided by its reusable mathematical owner. -/
#check (AlgebraicGeometry.ChernClass.Theory :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (δ : S → ℤ)
    [AlgebraicGeometry.UniversallyCatenary S] [IsDimensionFunction δ]
    {X : AlgebraicGeometry.Scheme.{u}} (p : X ⟶ S)
    [AlgebraicGeometry.LocallyOfFiniteType p], Type (u + 1))
