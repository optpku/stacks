/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.OpenMap
public import stacks_project.Chap101.Definition_101_13_2_Closed

/-!
# Open maps on points of algebraic stacks

A morphism of algebraic stacks induces an open map on underlying point spaces
when `Points.map f` is open for every pair of canonical topologies. Competing
topologies remain explicit parameters, parallel to `isClosedMapOnPoints`.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

open AlgebraicGeometry.AlgebraicStack

#check (AlgebraicGeometry.AlgebraicStack.isOpenMapOnPoints :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    (τX : TopologicalSpace (Points X)) (τY : TopologicalSpace (Points Y))
    (f : X ⟶ Y), Prop)

#check (AlgebraicGeometry.AlgebraicStack.isOpenMapOnPoints_iff :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    (τX : TopologicalSpace (Points X)) (τY : TopologicalSpace (Points Y))
    (f : X ⟶ Y),
    isOpenMapOnPoints τX τY f ↔
      ∀ (U : Set (Points X)),
        @IsOpen (Points X) τX U →
          @IsOpen (Points Y) τY (Points.map f '' U))

#check (AlgebraicGeometry.AlgebraicStack.pointsIsOpenMap :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y), Prop)

#check (AlgebraicGeometry.AlgebraicStack.pointsIsOpenMap_iff :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
    pointsIsOpenMap f ↔
      ∀ (τX : TopologicalSpace (Points X)) (τY : TopologicalSpace (Points Y)),
        IsPointsTopology X τX → IsPointsTopology Y τY →
          isOpenMapOnPoints τX τY f)
