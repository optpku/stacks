module

public import ReasLib.AlgebraicGeometry.Scheme.K0.VectorBundle.Pullback

open CategoryTheory

universe u

/- The compatibility module exposes pullback on vector-bundle `K₀`. -/
#check (AlgebraicGeometry.Scheme.VectorBundleK0.pullback :
  {X Y : AlgebraicGeometry.Scheme.{u}} →
    (X ⟶ Y) →
      AlgebraicGeometry.Scheme.VectorBundleK0 Y →+*
        AlgebraicGeometry.Scheme.VectorBundleK0 X)
