/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Closed

/-!
# Closed images on point spaces

A closed morphism of algebraic stacks has closed image on canonical point spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.Closed

/-- A closed morphism of algebraic stacks has closed image of points, for any
pair of canonical topologies on the source and target. -/
theorem isClosed_range_points {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Closed f]
    {τX : TopologicalSpace (Points X)} {τY : TopologicalSpace (Points Y)}
    (hX : IsPointsTopology X τX) (hY : IsPointsTopology Y τY) :
    @IsClosed (Points Y) τY (Set.range (Points.map f)) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.Closed
