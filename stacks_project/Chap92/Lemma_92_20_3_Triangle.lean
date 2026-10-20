module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.CotangentComplex.Transitivity

open CategoryTheory

universe u

#check (AlgebraicGeometry.RingedSpace.transitivityTriangle :
  ∀ {X Y Z : AlgebraicGeometry.RingedSpace.{u}} (_f : X ⟶ Y) (_g : Y ⟶ Z),
    CategoryTheory.Pretriangulated.Triangle (DerivedCategory X.Modules))
