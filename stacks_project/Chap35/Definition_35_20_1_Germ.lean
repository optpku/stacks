module

public import ReasLib.AlgebraicGeometry.Scheme.Germ

@[expose] public section

/- Compatibility check for constructing a scheme germ from a scheme and a point. -/
#check (AlgebraicGeometry.Scheme.Germ.of :
  (X : AlgebraicGeometry.Scheme) → X → AlgebraicGeometry.Scheme.Germ)
