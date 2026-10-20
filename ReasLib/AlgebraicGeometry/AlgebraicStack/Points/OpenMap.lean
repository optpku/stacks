/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.Topology

/-!
# Open maps on points of algebraic stacks

Openness of the canonical map on point spaces can be expressed using either
the canonical topologies or explicitly supplied topologies.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The map on points induced by `f` is an open map with respect to the given
topologies on the source and target point spaces. -/
def isOpenMapOnPoints {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    (τX : TopologicalSpace (Points X)) (τY : TopologicalSpace (Points Y))
    (f : X ⟶ Y) : Prop :=
  @IsOpenMap (Points X) (Points Y) τX τY (Points.map f)

/-- Being an open map on points means open sets in the source point space have
open images in the target. -/
theorem isOpenMapOnPoints_iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    (τX : TopologicalSpace (Points X)) (τY : TopologicalSpace (Points Y))
    (f : X ⟶ Y) :
    isOpenMapOnPoints τX τY f ↔
      ∀ (U : Set (Points X)),
        @IsOpen (Points X) τX U →
          @IsOpen (Points Y) τY (Points.map f '' U) :=
  Iff.rfl

/-- A morphism of algebraic stacks induces an open map on canonical point
spaces. -/
def pointsIsOpenMap {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop :=
  isOpenMapOnPoints (Points.topology X) (Points.topology Y) f

/-- A morphism induces an open map on points if it does so for every pair of
canonical topologies on the source and target. -/
theorem pointsIsOpenMap_iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    pointsIsOpenMap f ↔
      ∀ (τX : TopologicalSpace (Points X)) (τY : TopologicalSpace (Points Y)),
        IsPointsTopology X τX → IsPointsTopology Y τY →
          isOpenMapOnPoints τX τY f :=
  sorry

end AlgebraicGeometry.AlgebraicStack
