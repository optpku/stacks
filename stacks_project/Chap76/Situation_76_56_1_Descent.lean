module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ResolutionProperty.Descent

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.ResolutionDescent :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [IsQuasiCompact X]
    [IsAbsolutelyQuasiSeparated X], Type (u + 1))
