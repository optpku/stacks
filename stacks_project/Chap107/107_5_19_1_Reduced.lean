module

public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.Sets.Closeds
public import stacks_project.Chap100.Definition_100_4_2_Points
public import stacks_project.Chap100.Lemma_100_9_10_Substack
public import stacks_project.Chap100.Lemma_100_11_2_Reduced
public import stacks_project.Chap100.Lemma_100_11_3_LocallyNoetherian
public import stacks_project.Chap101.Definition_101_13_2_Closed

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Substack.IrreducibleComponent

/-!
# Reduced induced irreducible components

The canonical reduced induced component construction and its point specifications
are re-exported here together with the historical substack imports.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]

/- 107.5.19.1: Irreducible components carry their canonical reduced induced structure. -/
#check (AlgebraicGeometry.AlgebraicStack.irreducibleComponentSubstack :
  ∀ {τ : TopologicalSpace (Points X)} (hτ : IsPointsTopology X τ)
    (T : @irreducibleComponents (Points X) τ),
    ClosedSubstackStructure (irreducibleComponentClosed hτ T))

#check (AlgebraicGeometry.AlgebraicStack.irreducibleComponentClosed :
  ∀ {τ : TopologicalSpace (Points X)} (hτ : IsPointsTopology X τ)
    (T : @irreducibleComponents (Points X) τ), @Closeds (Points X) (Points.topology X))

#check (AlgebraicGeometry.AlgebraicStack.mem_irreducibleComponentClosed :
  ∀ {τ : TopologicalSpace (Points X)} (hτ : IsPointsTopology X τ)
    (T : @irreducibleComponents (Points X) τ) {x : Points X},
    x ∈ (irreducibleComponentClosed hτ T : Set (Points X)) ↔ x ∈ (T : Set (Points X)))

#check (AlgebraicGeometry.AlgebraicStack.mem_pointsSet_irreducibleComponentSubstack :
  ∀ {τ : TopologicalSpace (Points X)} (hτ : IsPointsTopology X τ)
    (T : @irreducibleComponents (Points X) τ) {x : Points X}
    (hx : x ∈ (T : Set (Points X))),
    x ∈ Set.range (Points.map (irreducibleComponentSubstack hτ T).ι))

#check (AlgebraicGeometry.AlgebraicStack.irreducibleComponentSubstack.point :
  ∀ {τ : TopologicalSpace (Points X)} (hτ : IsPointsTopology X τ)
    (T : @irreducibleComponents (Points X) τ) (x : Points X)
    (hx : x ∈ (T : Set (Points X))), Points (irreducibleComponentSubstack hτ T).Y)

#check (AlgebraicGeometry.AlgebraicStack.irreducibleComponentSubstack.point_map :
  ∀ {τ : TopologicalSpace (Points X)} (hτ : IsPointsTopology X τ)
    (T : @irreducibleComponents (Points X) τ) (x : Points X)
    (hx : x ∈ (T : Set (Points X))),
    Points.map (irreducibleComponentSubstack hτ T).ι
      (irreducibleComponentSubstack.point hτ T x hx) = x)

end AlgebraicGeometry.AlgebraicStack
