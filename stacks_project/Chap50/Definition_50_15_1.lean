/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.RingedSpace.DeRham.LogPole

universe u

/- Definition 50.15.1: for an effective Cartier divisor `Y ⟶ X` over `S`, the de Rham
complex of log poles is defined when, at every point of `Y` and for every local equation `a`,
the map `g ↦ g • da` is split injective and multiplication by `a` is injective on every
stalk of relative differential forms. -/
@[stacks 0FMV] #check
  (@AlgebraicGeometry.RingedSpace.DeRham.LogPole.IsDefined :
    {S X Y : AlgebraicGeometry.Scheme.{u}} → (X ⟶ S) → (i : Y ⟶ X) →
      [AlgebraicGeometry.IsEffectiveCartierDivisor i] → Prop)
