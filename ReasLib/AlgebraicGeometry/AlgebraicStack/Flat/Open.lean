/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.OpenMap
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation

/-!
# Flat locally of finite presentation morphisms are open on points

A flat morphism of algebraic stacks that is locally of finite presentation
induces an open map on canonical point spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A flat morphism of algebraic stacks that is locally of finite presentation
induces an open map on canonical point spaces. -/
@[stacks 06R7]
theorem Flat.pointsIsOpenMap {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [Flat f] [LocallyOfFinitePresentation f] : pointsIsOpenMap f :=
  sorry

/-- A flat locally of finite presentation morphism of algebraic stacks induces an
open map on points for any pair of canonical topologies. -/
theorem Flat.isOpenMapOnPoints {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [Flat f] [LocallyOfFinitePresentation f]
    {τX : TopologicalSpace (Points X)} {τY : TopologicalSpace (Points Y)}
    (hX : IsPointsTopology X τX) (hY : IsPointsTopology Y τY) :
    isOpenMapOnPoints τX τY f :=
  sorry

/-- The image of an open set of points under a flat locally of finite
presentation morphism of algebraic stacks is open. -/
theorem Flat.isOpen_image {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [Flat f] [LocallyOfFinitePresentation f]
    {τX : TopologicalSpace (Points X)} {τY : TopologicalSpace (Points Y)}
    (hX : IsPointsTopology X τX) (hY : IsPointsTopology Y τY)
    {U : Set (Points X)} (hU : @IsOpen (Points X) τX U) :
    @IsOpen (Points Y) τY (Points.map f '' U) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
