/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.K0.VectorBundle.Adams

universe u

/- The compatibility module exposes the second Adams ring endomorphism. -/
#check (AlgebraicGeometry.Scheme.VectorBundleK0.adamsTwo :
  (X : AlgebraicGeometry.Scheme.{u}) →
    AlgebraicGeometry.Scheme.VectorBundleK0 X →+*
      AlgebraicGeometry.Scheme.VectorBundleK0 X)
