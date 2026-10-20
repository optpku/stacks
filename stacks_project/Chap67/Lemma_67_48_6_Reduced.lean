module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Reduced

/-! # Reduced algebraic spaces

The canonical public owner defines reducedness by a reduced étale scheme atlas and records
its equivalent universal chart condition. This helper re-exports that unchanged interface.
-/

universe u

#check (AlgebraicGeometry.AlgebraicSpace.IsReduced :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}, AlgebraicGeometry.AlgebraicSpace S → Prop)
