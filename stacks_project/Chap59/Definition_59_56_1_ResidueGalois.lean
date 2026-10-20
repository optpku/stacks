module

public import ReasLib.AlgebraicGeometry.Scheme.GeometricPoint.ResidueGalois

@[expose] public section

universe u

#check (AlgebraicGeometry.Scheme.GeometricPoint.separableClosure :
  {S : AlgebraicGeometry.Scheme.{u}} →
    (s : AlgebraicGeometry.Scheme.GeometricPoint S) →
      IntermediateField (S.residueField s.toFieldValuedPoint.image) s.K)
