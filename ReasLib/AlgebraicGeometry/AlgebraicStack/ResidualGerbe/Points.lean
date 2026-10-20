/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.ResidualGerbe

/-!
# Field-valued points of residual gerbes

A field-valued point represents the marked point of a residual gerbe if and
only if it factors through the residual-gerbe inclusion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.IsResidualGerbe

/-- Every field-valued point representing `x` factors through a residual-gerbe
inclusion at `x`, up to a 2-isomorphism and over the same field. -/
@[stacks 06MW]
theorem factorsThrough {S : Scheme.{u}} {X Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Z] {ι : Z ⟶ X} {x : Points X}
    [IsResidualGerbe ι x] (f : FieldValuedPoint X) (hf : Points.mk f = x) :
    ∃ g : GroupoidsOver.slice f.overObj ⟶ Z, Nonempty (g ≫ ι ≅ f.hom) :=
  sorry

/-- A field-valued point of `X` factors through a residual gerbe at `x` if and
only if it represents `x`. -/
theorem factorsThrough_iff {S : Scheme.{u}} {X Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Z] {ι : Z ⟶ X} {x : Points X}
    [IsResidualGerbe ι x] (f : FieldValuedPoint X) :
    (∃ g : GroupoidsOver.slice f.overObj ⟶ Z, Nonempty (g ≫ ι ≅ f.hom)) ↔
      Points.mk f = x :=
  sorry

end AlgebraicGeometry.AlgebraicStack.IsResidualGerbe
