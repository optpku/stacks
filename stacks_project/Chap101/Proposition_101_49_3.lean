/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Sober
public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.AbsoluteTransformations.Maps
public import stacks_project.Chap101.Definition_101_13_2_Closed
public import stacks_project.Chap101.Definition_101_50_1_Decent
public import stacks_project.Chap101.Lemma_101_5_1

/-!
# Sober points of decent algebraic stacks with quasi-compact inertia

The points space of a decent algebraic stack whose inertia morphism is
quasi-compact is sober in the sense of Topology, Definition 5.8.6.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicStack
open FiberedCategoryOver.Groupoids.Inertia (forget)
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.IsDecent

/-- Proposition 101.49.3: Let `X` be a decent algebraic stack such that the
inertia morphism `I_X ⟶ X` is quasi-compact. Then `|X|` is sober, i.e.
`@T0Space (Points X) τ` and `@QuasiSober (Points X) τ` for every canonical
`IsPointsTopology`. -/
@[stacks 0GW9]
theorem sober_of_quasiCompact_inertia {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [IsDecent X]
    [QuasiCompact (forget.{u + 1, u, u, u + 1} X)]
    (τ : TopologicalSpace (Points X)) (hτ : IsPointsTopology X τ) :
    @T0Space (Points X) τ ∧ @QuasiSober (Points X) τ :=
  sorry

/-- Every irreducible closed subset of the points space of a decent algebraic
stack with quasi-compact inertia morphism has a unique generic point. -/
theorem existsUnique_isGenericPoint_of_quasiCompact_inertia
    {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] [IsDecent X]
    [QuasiCompact (forget.{u + 1, u, u, u + 1} X)]
    {τ : TopologicalSpace (Points X)} (hτ : IsPointsTopology X τ)
    {T : Set (Points X)} (hT_irred : @IsIrreducible (Points X) τ T)
    (hT_closed : @IsClosed (Points X) τ T) :
    ∃! x, @IsGenericPoint (Points X) τ x T :=
  sorry

end AlgebraicGeometry.AlgebraicStack.IsDecent
