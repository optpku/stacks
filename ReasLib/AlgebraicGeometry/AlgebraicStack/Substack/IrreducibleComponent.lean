module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Reduction
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Substack.Noetherian
public import Mathlib.Topology.Irreducible

/-!
# Reduced induced structures on irreducible components

An irreducible component of the point space carries its reduced induced closed
substack structure. Every point of the component lifts along its inclusion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]

/-- An irreducible component is a closed subset in the canonical topology on points. -/
def irreducibleComponentClosed {τ : TopologicalSpace (Points X)}
    (hτ : IsPointsTopology X τ) (T : @irreducibleComponents (Points X) τ) :
    @Closeds (Points X) (Points.topology X) :=
  @Closeds.mk (Points X) (Points.topology X) (T : Set (Points X)) (by
    have hclosed :=
      @isClosed_of_mem_irreducibleComponents (Points X) τ (T : Set (Points X)) T.2
    exact (isPointsTopology_unique hτ (isPointsTopology_pointsTopology X)) ▸ hclosed)

/-- The canonical closed subset of a component has exactly the component's points. -/
theorem mem_irreducibleComponentClosed {τ : TopologicalSpace (Points X)}
    (hτ : IsPointsTopology X τ) (T : @irreducibleComponents (Points X) τ)
    {x : Points X} :
    x ∈ (irreducibleComponentClosed hτ T : Set (Points X)) ↔ x ∈ (T : Set (Points X)) :=
  Iff.rfl

/-- The reduced induced closed substack supported on an irreducible component. -/
@[reducible]
def irreducibleComponentSubstack {τ : TopologicalSpace (Points X)}
    (hτ : IsPointsTopology X τ) (T : @irreducibleComponents (Points X) τ) :
    ClosedSubstackStructure (irreducibleComponentClosed hτ T) :=
  ClosedSubstackStructure.reduced (irreducibleComponentClosed hτ T)

/-- Every point of a component is in the range of its reduced substack's inclusion. -/
theorem mem_pointsSet_irreducibleComponentSubstack {τ : TopologicalSpace (Points X)}
    (hτ : IsPointsTopology X τ) (T : @irreducibleComponents (Points X) τ)
    {x : Points X} (hx : x ∈ (T : Set (Points X))) :
    x ∈ Set.range (Points.map (irreducibleComponentSubstack hτ T).ι) := by
  rw [(ClosedSubstackStructure.reduced_spec (irreducibleComponentClosed hτ T)).1]
  exact hx

/-- A point of the reduced induced component lying over the given ambient point. -/
def irreducibleComponentSubstack.point {τ : TopologicalSpace (Points X)}
    (hτ : IsPointsTopology X τ) (T : @irreducibleComponents (Points X) τ)
    (x : Points X) (hx : x ∈ (T : Set (Points X))) :
    Points (irreducibleComponentSubstack hτ T).Y :=
  Classical.choose (mem_pointsSet_irreducibleComponentSubstack hτ T hx)

/-- The selected point of a reduced induced component maps to the ambient point. -/
theorem irreducibleComponentSubstack.point_map {τ : TopologicalSpace (Points X)}
    (hτ : IsPointsTopology X τ) (T : @irreducibleComponents (Points X) τ)
    (x : Points X) (hx : x ∈ (T : Set (Points X))) :
    Points.map (irreducibleComponentSubstack hτ T).ι
      (irreducibleComponentSubstack.point hτ T x hx) = x :=
  Classical.choose_spec (mem_pointsSet_irreducibleComponentSubstack hτ T hx)

end AlgebraicGeometry.AlgebraicStack
