/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.K0.VectorBundle

universe u

#check
  (AlgebraicGeometry.Scheme.VectorBundleK0.toK0 :
    (X : AlgebraicGeometry.Scheme.{u}) →
      AlgebraicGeometry.Scheme.VectorBundleK0 X →+
        AlgebraicGeometry.Scheme.K0 X)
