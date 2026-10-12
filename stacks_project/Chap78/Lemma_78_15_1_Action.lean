/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Action

/-!
# Action groupoids of algebraic spaces

This module provides the source-facing compatibility check for the internal
groupoid in algebraic spaces associated to an action of a group algebraic space.
-/

universe u

open AlgebraicGeometry

#check
  (GroupoidAlgebraicSpace.ofAction :
    {S : Scheme.{u}} → {B : AlgebraicSpace S} → (G : GroupAlgebraicSpace B) →
      GroupAlgebraicSpace.Action G → GroupoidAlgebraicSpace B)
