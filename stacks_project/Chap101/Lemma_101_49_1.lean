/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Separation.Basic
public import stacks_project.Chap101.Definition_101_13_2_Closed
public import stacks_project.Chap101.Definition_101_50_1_Decent

/-!
# Kolmogorov points of decent algebraic stacks

The points space of a decent algebraic stack is Kolmogorov in the sense of
Topology, Definition 5.8.6, i.e. a `T0Space` in every canonical
`IsPointsTopology`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicStack.IsDecent

/-- Lemma 101.49.1: Let `X` be a decent algebraic stack. Then `|X|` is Kolmogorov
in the sense of Topology, Definition 5.8.6, i.e. `@T0Space (Points X) τ` for
every canonical `IsPointsTopology`. -/
@[stacks 0GW7]
theorem t0Space {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    [IsDecent X] (τ : TopologicalSpace (Points X))
    (hτ : IsPointsTopology X τ) :
    @T0Space (Points X) τ :=
  sorry

/-- Mutual specialization of points of a decent algebraic stack implies equality. -/
theorem eq_of_specializes_specializes {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsDecent X] {τ : TopologicalSpace (Points X)}
    (hτ : IsPointsTopology X τ) {x x' : Points X}
    (h : @Specializes (Points X) τ x x')
    (h' : @Specializes (Points X) τ x' x) :
    x = x' :=
  sorry

end AlgebraicGeometry.AlgebraicStack.IsDecent
