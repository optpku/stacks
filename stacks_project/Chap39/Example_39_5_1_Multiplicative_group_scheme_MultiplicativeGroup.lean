module

public import ReasLib.AlgebraicGeometry.MultiplicativeGroup

open CategoryTheory
open AlgebraicGeometry

universe u

#check (AlgebraicGeometry.MultiplicativeGroup.groupScheme :
  CommGrp (Over (Spec (CommRingCat.of (ULift.{u} ℤ)))))
