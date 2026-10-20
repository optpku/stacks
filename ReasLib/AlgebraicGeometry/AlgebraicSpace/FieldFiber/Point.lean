/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FieldFiber

/-!
# Canonical points of field-valued fibres

A field-valued point of an algebraic space gives a rational point of the fibre over its
image under any morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The rational point of the fibre of `g` over the image of the field-valued point `p`. -/
def fieldFiberPoint {X Z : AlgebraicSpace S} (p : FieldValuedPoint X)
    (g : X ⟶ Z) : FieldValuedPoint (fieldFiber g (p.map g)) :=
  FieldValuedPoint.of p.K p.structureHom
    (pullback.lift p.hom (𝟙 (ofOver p.overObj)) (by
      change p.hom ≫ g = 𝟙 _ ≫ (p.hom ≫ g)
      rw [Category.id_comp]))

/-- The morphism of the canonical rational point is the universal lift of `p.hom` and the
identity of its source spectrum. -/
theorem fieldFiberPoint_hom {X Z : AlgebraicSpace S} (p : FieldValuedPoint X) (g : X ⟶ Z) :
    (fieldFiberPoint p g).hom =
      pullback.lift p.hom (𝟙 (ofOver p.overObj)) (by
        change p.hom ≫ g = 𝟙 _ ≫ (p.hom ≫ g)
        rw [Category.id_comp]) :=
  rfl

end AlgebraicGeometry.AlgebraicSpace
