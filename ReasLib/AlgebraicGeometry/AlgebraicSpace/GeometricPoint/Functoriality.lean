/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricPoint

/-!
# Functoriality of geometric points
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.GeometricPoint

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.GeometricPoint

/-- Postcomposition of geometric points is strictly functorial. -/
theorem map_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (xbar : GeometricPoint X)
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    xbar.map (f ≫ g) = (xbar.map f).map g :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.GeometricPoint
