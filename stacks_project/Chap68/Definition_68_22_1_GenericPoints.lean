module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.GenericPoints

#check (AlgebraicGeometry.AlgebraicSpace.genericPoints :
  {S : AlgebraicGeometry.Scheme} → (X : AlgebraicGeometry.AlgebraicSpace S) →
    Set (AlgebraicGeometry.AlgebraicSpace.Points X))
