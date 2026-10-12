/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.NormalCrossings.EtaleLocal

universe u

#check (@AlgebraicGeometry.IsNormalCrossingsDivisor :
  ∀ {X : AlgebraicGeometry.Scheme.{u}}, AlgebraicGeometry.IsLocallyNoetherian X →
    X.IdealSheafData → Prop)
