module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.NormalCrossings.EtaleLocal

universe u

#check (@AlgebraicGeometry.IsNormalCrossingsDivisor :
  ∀ {X : AlgebraicGeometry.Scheme.{u}}, AlgebraicGeometry.IsLocallyNoetherian X →
    X.IdealSheafData → Prop)
