/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.K0.Module

universe u

#check
  (AlgebraicGeometry.Scheme.K0'.instModule :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsNoetherian X],
      Module (AlgebraicGeometry.Scheme.K0 X) (AlgebraicGeometry.Scheme.K0' X))
