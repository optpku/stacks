module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Affine

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

#check (AlgebraicGeometry.GroupoidsOver.affineInclusion :
  ∀ {S : Scheme.{u}} (X : AlgebraicGeometry.GroupoidsOver S),
    AlgebraicGeometry.GroupoidsOver.Affine X ⥤ X.total)
