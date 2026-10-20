module

public import Mathlib.Topology.Separation.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Decent
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.Topology

/-!
# Kolmogorov points of decent algebraic stacks

The canonical space of points of a decent algebraic stack is Kolmogorov.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicStack.IsDecent

/-- Every canonical topology on the points of a decent algebraic stack is T₀. -/
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

/-- The canonical space of points of a decent algebraic stack is T₀. -/
instance instT0SpacePoints {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [IsDecent X] : T0Space (Points X) :=
  t0Space X (Points.topology X) (isPointsTopology_pointsTopology X)

end AlgebraicGeometry.AlgebraicStack.IsDecent
