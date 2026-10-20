module

public import ReasLib.AlgebraicGeometry.Scheme.K0.VectorBundle

universe u

#check
  (AlgebraicGeometry.Scheme.VectorBundleK0.toK0 :
    (X : AlgebraicGeometry.Scheme.{u}) →
      AlgebraicGeometry.Scheme.VectorBundleK0 X →+
        AlgebraicGeometry.Scheme.K0 X)
