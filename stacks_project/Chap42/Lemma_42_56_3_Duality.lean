module

public import ReasLib.AlgebraicGeometry.Scheme.K0.VectorBundle.Duality

universe u

/- The compatibility module exposes dualization on vector-bundle `K₀`. -/
#check (AlgebraicGeometry.Scheme.VectorBundleK0.dual :
  (X : AlgebraicGeometry.Scheme.{u}) →
    AlgebraicGeometry.Scheme.VectorBundleK0 X →+*
      AlgebraicGeometry.Scheme.VectorBundleK0 X)
