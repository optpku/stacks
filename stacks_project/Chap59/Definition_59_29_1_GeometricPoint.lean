module

public import ReasLib.AlgebraicGeometry.Scheme.GeometricPoint

open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

#check (AlgebraicGeometry.Scheme.GeometricPoint : Scheme.{u} → Type (u + 1))

#check (AlgebraicGeometry.Scheme.GeometricPoint.EtaleNeighborhood :
  {S : Scheme.{u}} → GeometricPoint S → Type (u + 1))

#check (AlgebraicGeometry.Scheme.GeometricPoint.EtaleNeighborhood.Hom :
  {S : Scheme.{u}} → {s : GeometricPoint S} →
    GeometricPoint.EtaleNeighborhood s → GeometricPoint.EtaleNeighborhood s → Type u)
