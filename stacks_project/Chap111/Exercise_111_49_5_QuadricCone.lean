module

public import ReasLib.AlgebraicGeometry.QuadricCone

universe u

/- The affine quadratic cone as a scheme over its coefficient field. -/
#check (AlgebraicGeometry.QuadricCone.overField :
  ∀ (k : Type u) [Field k], AlgebraicGeometry.SchemeOverField k)
