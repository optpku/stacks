module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.PointSum

open AlgebraicGeometry

universe u

#check (AlgebraicGeometry.Curve.pointSumDivisor :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k) [Curve X] {r : ℕ}
    (x : Fin r → X.left) (hx : ∀ i, x i ∈ closedPoints X.left),
    X.left.IdealSheafData)

#check (AlgebraicGeometry.Curve.instIsEffectiveCartierDivisor_pointSumDivisor :
  ∀ {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [Curve X] [Smooth X.hom] {r : ℕ}
    (x : Fin r → X.left) (hx : ∀ i, x i ∈ closedPoints X.left),
    IsEffectiveCartierDivisor (Curve.pointSumDivisor X x hx).subschemeι)
