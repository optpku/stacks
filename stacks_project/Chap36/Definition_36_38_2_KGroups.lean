/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.K0

universe u

#check
  (AlgebraicGeometry.Scheme.K0 : AlgebraicGeometry.Scheme.{u} → Type (u + 1))

#check
  (AlgebraicGeometry.Scheme.K0' :
    (X : AlgebraicGeometry.Scheme.{u}) →
      [AlgebraicGeometry.IsLocallyNoetherian X] → Type (u + 1))
