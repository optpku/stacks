module

public import ReasLib.AlgebraicGeometry.AdditiveGroup

open CategoryTheory
open AlgebraicGeometry

universe u

#check (AlgebraicGeometry.AdditiveGroup.groupScheme :
  (S : Scheme.{u}) → CommGrp (Over S))
