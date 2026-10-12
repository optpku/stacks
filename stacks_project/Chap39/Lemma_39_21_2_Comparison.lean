/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Cartesian.ActionEquivalence

universe u

/- Compatibility bridge for consumers of the former comparison module. -/
#check (AlgebraicGeometry.GroupoidScheme.CartesianOver.cartesianActionEquivalence :
  {S : AlgebraicGeometry.Scheme.{u}} →
    (G : AlgebraicGeometry.GroupoidScheme S) →
      AlgebraicGeometry.GroupoidScheme.CartesianOver G ≌
        AlgebraicGeometry.GroupoidScheme.Action G)
