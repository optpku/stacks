module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Differentials

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

#check (AlgebraicGeometry.AlgebraicSpace.Hom.relativeDifferentials f : X.Modules)
