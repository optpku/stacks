module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RationalMap.Basic

/-! Compatibility facade for the canonical public owner. -/

universe u

#check (AlgebraicGeometry.AlgebraicSpace.RationalMap :
  {S : AlgebraicGeometry.Scheme.{u}} →
    AlgebraicGeometry.AlgebraicSpace S → AlgebraicGeometry.AlgebraicSpace S → Type (u + 1))
