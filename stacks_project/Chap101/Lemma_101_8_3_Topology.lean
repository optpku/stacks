/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Noetherian.Basic
public import stacks_project.Chap101.Definition_101_8_1_Noetherian
public import stacks_project.Chap101.Definition_101_13_2_Closed

/-!
# Points of locally Noetherian algebraic stacks

The points space of a locally Noetherian algebraic stack is locally Noetherian, and it is
Noetherian when the algebraic stack is also quasi-compact.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicStack.IsLocallyNoetherian

/-- The points space of a locally Noetherian algebraic stack is a locally Noetherian topological
space. -/
theorem locallyNoetherianSpace {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [IsLocallyNoetherian X] (τ : TopologicalSpace (Points X))
    (hτ : IsPointsTopology X τ) :
    @TopologicalSpace.LocallyNoetherianSpace (Points X) τ :=
  sorry

/-- The points space of a quasi-compact locally Noetherian algebraic stack is a Noetherian
topological space. -/
theorem noetherianSpace {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [IsQuasiCompact X] [IsLocallyNoetherian X]
    (τ : TopologicalSpace (Points X)) (hτ : IsPointsTopology X τ) :
    @TopologicalSpace.NoetherianSpace (Points X) τ :=
  sorry

end AlgebraicGeometry.AlgebraicStack.IsLocallyNoetherian
