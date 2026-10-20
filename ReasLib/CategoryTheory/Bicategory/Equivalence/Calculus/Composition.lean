/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Equivalence.Calculus.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Composition of bicategorical equivalences

This leaf owns the canonical unit, counit, and adjoint-equivalence structure
for a composite of bicategorical equivalences.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Bicategory
open scoped Bicategory

variable {B : Type u} [Bicategory.{w, v} B]

namespace Bicategory.Equivalence

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

variable {x y z : B}

/-- The canonical unit of a composite bicategorical equivalence. -/
@[stacks 0040 "unit of a composite bicategorical equivalence"]
def trans.unitIso (e : x ≌ y) (f : y ≌ z) :
    𝟙 x ≅ (e.hom ≫ f.hom) ≫ (f.inv ≫ e.inv) :=
  e.unit ≪⊗≫
    whiskerRightIso (whiskerLeftIso e.hom f.unit) e.inv ≪⊗≫
      Iso.refl _

/-- The canonical counit of a composite bicategorical equivalence. -/
@[stacks 0040 "counit of a composite bicategorical equivalence"]
def trans.counitIso (e : x ≌ y) (f : y ≌ z) :
    (f.inv ≫ e.inv) ≫ (e.hom ≫ f.hom) ≅ 𝟙 z :=
  Iso.refl _ ≪⊗≫
    whiskerRightIso (whiskerLeftIso f.inv e.counit) f.hom ≪⊗≫
      f.counit

/-- The canonical unit and counit of a composite equivalence satisfy the left triangle
identity. -/
private theorem Implementation.trans.left_triangle (e : x ≌ y) (f : y ≌ z) :
    leftZigzagIso (trans.unitIso e f) (trans.counitIso e f) =
      λ_ (e.hom ≫ f.hom) ≪≫ (ρ_ (e.hom ≫ f.hom)).symm := sorry

/-- Compose bicategorical equivalences while retaining the canonical composite unit and
counit. -/
@[stacks 0040 "compose bicategorical equivalences"]
def trans (e : x ≌ y) (f : y ≌ z) : x ≌ z where
  hom := e.hom ≫ f.hom
  inv := f.inv ≫ e.inv
  unit := trans.unitIso e f
  counit := trans.counitIso e f
  left_triangle := Implementation.trans.left_triangle e f

/-- The forward `1`-morphism of a composite equivalence is the composite of the forward
`1`-morphisms. -/
@[simp]
theorem trans.hom (e : x ≌ y) (f : y ≌ z) :
    (e.trans f).hom = e.hom ≫ f.hom := sorry

/-- The inverse `1`-morphism of a composite equivalence is the reverse composite of the
inverse `1`-morphisms. -/
@[simp]
theorem trans.inv (e : x ≌ y) (f : y ≌ z) :
    (e.trans f).inv = f.inv ≫ e.inv := sorry

/-- The unit of a composite equivalence is the canonical composite unit. -/
@[simp]
theorem trans.unit (e : x ≌ y) (f : y ≌ z) :
    (e.trans f).unit = trans.unitIso e f := sorry

/-- The counit of a composite equivalence is the canonical composite counit. -/
@[simp]
theorem trans.counit (e : x ≌ y) (f : y ≌ z) :
    (e.trans f).counit = trans.counitIso e f := sorry

/-- Composition of equivalences becomes composition in the bicategory of adjunctions. -/
@[simp]
theorem toAdjHom.trans (e : x ≌ y) (e' : y ≌ z) :
    (e.trans e').toAdjHom =
      e.toAdjHom ≫ e'.toAdjHom := sorry

end Bicategory.Equivalence

end CategoryTheory
