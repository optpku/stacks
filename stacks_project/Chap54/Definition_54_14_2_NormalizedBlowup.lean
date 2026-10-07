module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Normalized

universe u

/- Normalized point blowups retain their explicit ordinary blowup and normalization data. -/
#check (AlgebraicGeometry.Scheme.NormalizedBlowup :
  AlgebraicGeometry.Scheme.{u} → Type (u + 1))
