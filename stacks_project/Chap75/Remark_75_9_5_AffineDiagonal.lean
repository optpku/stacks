module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.AbsoluteAffineDiagonal

/-!
# Absolute affine diagonal of algebraic spaces

An algebraic space has affine diagonal over the terminal scheme when the diagonal
of the space viewed over that scheme is a representable affine morphism.
-/

@[expose] public section

universe u

#check (AlgebraicGeometry.AlgebraicSpace.IsAbsolutelyAffineDiagonal :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}, AlgebraicGeometry.AlgebraicSpace S → Prop)
