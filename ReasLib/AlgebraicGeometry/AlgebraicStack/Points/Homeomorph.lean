module

public import Mathlib.Topology.Homeomorph.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.Topology

/-!
# Homeomorphisms on points of algebraic stacks

Homeomorphisms on point spaces can be tested with explicit topologies or with
the canonical atlas-tested topologies.
-/

@[expose] public section

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
  isHomeomorphOnPoints (Points.topology X) (Points.topology Y) f

/-- A morphism induces a homeomorphism on points if it does so for every pair of
canonical topologies on the source and target. -/
theorem pointsIsHomeomorph_iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    pointsIsHomeomorph f ↔
      ∀ (τX : TopologicalSpace (Points X)) (τY : TopologicalSpace (Points Y)),
        IsPointsTopology X τX → IsPointsTopology Y τY →
          isHomeomorphOnPoints τX τY f :=
  sorry

/-- Composition of morphisms that induce homeomorphisms on canonical point
spaces again induces a homeomorphism on canonical point spaces. -/
theorem pointsIsHomeomorph_comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z] {f : X ⟶ Y}
    {g : Y ⟶ Z} (hf : pointsIsHomeomorph f) (hg : pointsIsHomeomorph g) :
    pointsIsHomeomorph (f ≫ g) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
