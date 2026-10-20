module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Irreducible

/-! Compatibility facade for the canonical algebraic-space property. -/

universe u

#check (AlgebraicGeometry.AlgebraicSpace.IsIrreducible :
  {S : AlgebraicGeometry.Scheme.{u}} → AlgebraicGeometry.AlgebraicSpace S → Prop)
