module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

@[expose] public section

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AffineSpace

/-- The projection from a finite-dimensional affine space to its base scheme is smooth. -/
instance smooth_over (n : Type u) [Finite n] (S : Scheme.{u}) :
    Smooth (𝔸(n; S) ↘ S) := sorry

end AlgebraicGeometry.AffineSpace
