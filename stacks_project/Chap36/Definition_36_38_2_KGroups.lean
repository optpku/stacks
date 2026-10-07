module

public import ReasLib.AlgebraicGeometry.Scheme.K0

universe u

#check
  (AlgebraicGeometry.Scheme.K0 : AlgebraicGeometry.Scheme.{u} → Type (u + 1))

#check
  (AlgebraicGeometry.Scheme.K0' :
    (X : AlgebraicGeometry.Scheme.{u}) →
      [AlgebraicGeometry.IsLocallyNoetherian X] → Type (u + 1))
