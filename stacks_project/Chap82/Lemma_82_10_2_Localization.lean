module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.Localization

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Hom.Localization.complex :
  ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
    (f : X ⟶ B) [LocallyOfFiniteType f] (δ : Points B → ℤ)
    (U : OpenSubspace X) (k : ℤ), ShortComplex Ab.{u + 1})
