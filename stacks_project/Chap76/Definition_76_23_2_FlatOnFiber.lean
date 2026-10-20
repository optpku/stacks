/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.Fiberwise

/-!
# Fibrewise relative flatness of modules on algebraic spaces

In a triangle `X ⟶ Y ⟶ Z` of algebraic spaces, a module on `X` is flat at a point of
`|X|` on the fibre over `Z` relative to the fibre of `Y` when the field-valued fibre
condition holds.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}

namespace Modules

/-- The restriction of `F` to the fibre of `X` over the image of `x` in `|Z|` is flat at
`x` over the fibre of `Y`, tested on the field-valued fibre product. -/
abbrev flatOnFiberAt (F : X.Modules) (f : X ⟶ Y) (h : Y ⟶ Z) (x : Points X) : Prop :=
  flatOnFiberAt_field F f h x

end Modules

end AlgebraicGeometry.AlgebraicSpace
