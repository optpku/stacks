module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Presentation

@[expose] public section

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Presentation :
  {S : AlgebraicGeometry.Scheme.{u}} → AlgebraicGeometry.AlgebraicSpace S → Type (u + 1))
