/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Limit.FiniteTypeApproximation.Diagram
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u

/- 70.23.2.1: the commuting square of algebraic spaces through the intermediate space `W`. -/
@[stacks 0CP8] #check
  (AlgebraicGeometry.AlgebraicSpace.FiniteTypeApproximationDiagram :
    {S : Scheme.{u}} → {X B Bi : AlgebraicSpace S} →
      (X ⟶ B) → (B ⟶ Bi) → Type (u + 1))
