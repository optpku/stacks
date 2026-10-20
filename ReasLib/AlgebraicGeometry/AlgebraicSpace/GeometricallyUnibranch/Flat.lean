/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricallyUnibranch
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Flat

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.GeometricallyUnibranchAt

/-- Geometric unibranchness descends at a point along a morphism that is flat there. -/
theorem of_flatAt {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (x : Points X)
    (hf : FlatAt f x) [GeometricallyUnibranchAt X x] :
    GeometricallyUnibranchAt Y (Points.map f x) := sorry

end AlgebraicGeometry.AlgebraicSpace.GeometricallyUnibranchAt
