module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Line.Divisor

universe u

#check (AlgebraicGeometry.ProjectiveLine.Relative.zeroDivisor :
  (S : AlgebraicGeometry.Scheme.{u}) →
    (AlgebraicGeometry.ProjectiveSpace 1 S).IdealSheafData)

#check (AlgebraicGeometry.ProjectiveLine.Relative.infinityDivisor :
  (S : AlgebraicGeometry.Scheme.{u}) →
    (AlgebraicGeometry.ProjectiveSpace 1 S).IdealSheafData)
