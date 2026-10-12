/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Limit.FiniteTypeApproximation.Diagram

open AlgebraicGeometry CategoryTheory

universe u

/- 32.22.2.1: the commuting square through the intermediate scheme `W`. -/
@[stacks 0CNP] #check
  (AlgebraicGeometry.FiniteTypeApproximationDiagram :
    {X S Si : Scheme.{u}} → (X ⟶ S) → (S ⟶ Si) → Type (u + 1))
