module

public import ReasLib.AlgebraicGeometry.GroupoidScheme

universe u

#check (AlgebraicGeometry.GroupoidScheme :
  (S : AlgebraicGeometry.Scheme.{u}) → Type (u + 1))

#check (AlgebraicGeometry.GroupoidScheme.Hom :
  {S : AlgebraicGeometry.Scheme.{u}} →
    AlgebraicGeometry.GroupoidScheme S → AlgebraicGeometry.GroupoidScheme S → Type u)
