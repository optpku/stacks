module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FormalGlueing.Spaces

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.FormalGlueing.functor :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X),
    [IsClosedImmersion i] → Over X ⥤ AlgebraicGeometry.AlgebraicSpace.FormalGlueing.category f i)
