module

public import ReasLib.AlgebraicGeometry.AffineTriangle.Scheme

/-!
# The affine triangle `Spec (k[x, y] / (x * y * (x + y + 1)))`

This source-facing module preserves a typed construction check for the
affine triangle owned by `ReasLib.AlgebraicGeometry.AffineTriangle.Scheme`.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry

namespace AlgebraicGeometry.AffineTriangle

#check (AlgebraicGeometry.AffineTriangle.scheme :
  ∀ (k : Type u) [Field k], Scheme.{u})

end AlgebraicGeometry.AffineTriangle
