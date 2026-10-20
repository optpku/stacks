module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RationalFunction.Basic

/-! Compatibility facade for the canonical public owner. -/

universe u

#check (AlgebraicGeometry.AlgebraicSpace.RationalFunction :
  {S : AlgebraicGeometry.Scheme.{u}} → AlgebraicGeometry.AlgebraicSpace S → Type (u + 1))
