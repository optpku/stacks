module

public import ReasLib.AlgebraicGeometry.Scheme.K0.Module

universe u

#check
  (AlgebraicGeometry.Scheme.K0'.instModule :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsNoetherian X],
      Module (AlgebraicGeometry.Scheme.K0 X) (AlgebraicGeometry.Scheme.K0' X))
