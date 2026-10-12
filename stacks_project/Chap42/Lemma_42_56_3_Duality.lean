/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.K0.VectorBundle.Duality

universe u

/- The compatibility module exposes dualization on vector-bundle `K₀`. -/
#check (AlgebraicGeometry.Scheme.VectorBundleK0.dual :
  (X : AlgebraicGeometry.Scheme.{u}) →
    AlgebraicGeometry.Scheme.VectorBundleK0 X →+*
      AlgebraicGeometry.Scheme.VectorBundleK0 X)
