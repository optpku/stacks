/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsScheme
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening

/-!
# Scheme representability under thickening

A thickening of an algebraic space representable by a scheme is representable
by a scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsScheme

/-- If the source of a thickening of algebraic spaces over a scheme is
representable by a scheme, then so is its target. -/
theorem of_thickening {S : Scheme.{u}} {X X' : AlgebraicSpace S} (i : X ⟶ X')
    [IsThickening i] [IsScheme X] : IsScheme X' :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsScheme
