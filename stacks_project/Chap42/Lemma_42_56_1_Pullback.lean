/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

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
