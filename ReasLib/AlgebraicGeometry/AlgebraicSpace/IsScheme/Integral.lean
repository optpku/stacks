/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsScheme
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsScheme

/-- An integral morphism of algebraic spaces over a scheme that is bijective on
points has scheme source if and only if it has scheme target. -/
theorem iff_of_isIntegralHom {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsIntegralHom f] (hf : Function.Bijective (Points.map f)) :
    IsScheme X ↔ IsScheme Y :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsScheme
