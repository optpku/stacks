module

public import Mathlib.Topology.Homeomorph.Defs
public import stacks_project.Chap101.Definition_101_13_2_Closed

/-!
# Homeomorphisms on points of algebraic stacks

A morphism of algebraic stacks induces a homeomorphism on underlying point
spaces when `Points.map f` is a homeomorphism for every pair of canonical
topologies. Competing topologies remain explicit parameters, parallel to
`isOpenMapOnPoints`.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The map on points induced by `f` is a homeomorphism with respect to the given
topologies on the source and target point spaces. -/
def isHomeomorphOnPoints {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    (τX : TopologicalSpace (Points X)) (τY : TopologicalSpace (Points Y))
    (f : X ⟶ Y) : Prop :=
  @IsHomeomorph (Points X) (Points Y) τX τY (Points.map f)

/-- Being a homeomorphism on points means the induced map is continuous, open, and
bijective for the given topologies. -/
theorem isHomeomorphOnPoints_iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    (τX : TopologicalSpace (Points X)) (τY : TopologicalSpace (Points Y))
    (f : X ⟶ Y) :
    isHomeomorphOnPoints τX τY f ↔
      @Continuous (Points X) (Points Y) τX τY (Points.map f) ∧
        @IsOpenMap (Points X) (Points Y) τX τY (Points.map f) ∧
          Function.Bijective (Points.map f) :=
  sorry

/-- A morphism of algebraic stacks induces a homeomorphism on canonical point
spaces. -/
def pointsIsHomeomorph {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop :=
  ∀ (τX : TopologicalSpace (Points X)) (τY : TopologicalSpace (Points Y)),
    IsPointsTopology X τX → IsPointsTopology Y τY → isHomeomorphOnPoints τX τY f

/-- A morphism induces a homeomorphism on points if it does so for every pair of
canonical topologies on the source and target. -/
theorem pointsIsHomeomorph_iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    pointsIsHomeomorph f ↔
      ∀ (τX : TopologicalSpace (Points X)) (τY : TopologicalSpace (Points Y)),
        IsPointsTopology X τX → IsPointsTopology Y τY →
          isHomeomorphOnPoints τX τY f :=
  sorry

end AlgebraicGeometry.AlgebraicStack
