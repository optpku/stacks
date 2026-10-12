/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Sober
public import stacks_project.Chap101.Definition_101_8_1_Noetherian
public import stacks_project.Chap101.Definition_101_13_2_Closed

/-!
# Quasi-sobriety of points of locally Noetherian algebraic stacks

The points space of a locally Noetherian algebraic stack is quasi-sober:
every irreducible closed subset has a generic point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicStack.IsLocallyNoetherian

/-- The points space of a locally Noetherian algebraic stack is quasi-sober. -/
theorem quasiSober {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [IsLocallyNoetherian X] (τ : TopologicalSpace (Points X))
    (hτ : IsPointsTopology X τ) :
    @QuasiSober (Points X) τ :=
  sorry

/-- Every irreducible closed subset of the points space of a locally Noetherian
algebraic stack has a generic point. -/
theorem exists_isGenericPoint {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsLocallyNoetherian X] {τ : TopologicalSpace (Points X)}
    (hτ : IsPointsTopology X τ) {T : Set (Points X)}
    (hT_irred : @IsIrreducible (Points X) τ T)
    (hT_closed : @IsClosed (Points X) τ T) :
    ∃ x, @IsGenericPoint (Points X) τ x T :=
  sorry

end AlgebraicGeometry.AlgebraicStack.IsLocallyNoetherian
