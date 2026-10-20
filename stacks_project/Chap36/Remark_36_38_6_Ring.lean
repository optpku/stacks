module

public import ReasLib.AlgebraicGeometry.Scheme.K0.Ring
public import ReasLib.AlgebraicGeometry.Scheme.K0.VectorBundle.Ring

universe u

#check
  (AlgebraicGeometry.Scheme.K0.instCommRing :
    ∀ X : AlgebraicGeometry.Scheme.{u},
      CommRing (AlgebraicGeometry.Scheme.K0 X))

#check
  (AlgebraicGeometry.Scheme.VectorBundleK0.instCommRing :
    ∀ X : AlgebraicGeometry.Scheme.{u},
      CommRing (AlgebraicGeometry.Scheme.VectorBundleK0 X))

#check
  (AlgebraicGeometry.Scheme.VectorBundleK0.toK0RingHom :
    ∀ X : AlgebraicGeometry.Scheme.{u},
      AlgebraicGeometry.Scheme.VectorBundleK0 X →+*
        AlgebraicGeometry.Scheme.K0 X)
