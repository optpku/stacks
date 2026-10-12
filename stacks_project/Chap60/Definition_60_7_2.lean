/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.DividedPowers.Scheme
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 60.7.2 -/
@[stacks 07I3] #check (DividedPowerScheme.{u} : Type (u + 1))

/- Definition 60.7.2 (2): morphisms preserve the ideal sheaves and the
divided-power operations on sections. -/
@[stacks 07I3] #check (DividedPowerScheme.Hom.{u} :
  DividedPowerScheme.{u} → DividedPowerScheme.{u} → Type u)
