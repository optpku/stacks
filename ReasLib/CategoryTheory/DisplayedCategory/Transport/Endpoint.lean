/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DisplayedCategory.Structure

/-!
# Endpoint transport for displayed morphisms

This leaf owns transport of a displayed morphism when its base arrow is fixed and only its
displayed source and target are reindexed.  It is separate from base-arrow transport so callers
can import exactly the dependent equality API they need.
-/

@[expose] public section

universe v u w₁ w₂

namespace CategoryTheory.DisplayedCategory

variable {C : Type u} [Category.{v} C]
variable (D : DisplayedCategory C)

namespace Hom

/-- Transport a displayed morphism along equalities of its displayed endpoints. -/
def cast_obj {X Y : C} {f : X ⟶ Y} {x x' : D.obj X} {y y' : D.obj Y}
    (hx : x = x') (hy : y = y') (φ : D.Hom f x y) : D.Hom f x' y' :=
  hy ▸ hx ▸ φ

/-- Endpoint transport along reflexivity leaves a displayed morphism unchanged. -/
@[simp]
theorem cast_obj_rfl {X Y : C} {f : X ⟶ Y} {x : D.obj X} {y : D.obj Y}
    (φ : D.Hom f x y) : cast_obj D rfl rfl φ = φ := sorry

/-- Successive endpoint transports combine by transitivity of the endpoint equalities. -/
theorem cast_obj_trans {X Y : C} {f : X ⟶ Y}
    {x x' x'' : D.obj X} {y y' y'' : D.obj Y}
    (hx : x = x') (hx' : x' = x'') (hy : y = y') (hy' : y' = y'')
    (φ : D.Hom f x y) :
    cast_obj D hx' hy' (cast_obj D hx hy φ) =
      cast_obj D (hx.trans hx') (hy.trans hy') φ := sorry

/-- Forward endpoint transport followed by the reverse transport recovers the morphism. -/
@[simp]
theorem cast_obj_symm_apply {X Y : C} {f : X ⟶ Y}
    {x x' : D.obj X} {y y' : D.obj Y} (hx : x = x') (hy : y = y')
    (φ : D.Hom f x y) :
    cast_obj D hx.symm hy.symm (cast_obj D hx hy φ) = φ := sorry

/-- Reverse endpoint transport followed by the forward transport recovers the morphism. -/
@[simp]
theorem cast_obj_apply_symm {X Y : C} {f : X ⟶ Y}
    {x x' : D.obj X} {y y' : D.obj Y} (hx : x = x') (hy : y = y')
    (φ : D.Hom f x' y') :
    cast_obj D hx hy (cast_obj D hx.symm hy.symm φ) = φ := sorry

/-- Equality of displayed endpoints induces an equivalence of the corresponding hom types. -/
def castObjEquiv {X Y : C} {f : X ⟶ Y}
    {x x' : D.obj X} {y y' : D.obj Y} (hx : x = x') (hy : y = y') :
    D.Hom f x y ≃ D.Hom f x' y' where
  toFun := cast_obj D hx hy
  invFun := cast_obj D hx.symm hy.symm
  left_inv := cast_obj_symm_apply D hx hy
  right_inv := cast_obj_apply_symm D hx hy

/-- Applying the endpoint-transport equivalence is canonical endpoint transport. -/
@[simp]
theorem castObjEquiv_apply {X Y : C} {f : X ⟶ Y}
    {x x' : D.obj X} {y y' : D.obj Y} (hx : x = x') (hy : y = y')
    (φ : D.Hom f x y) :
    castObjEquiv D hx hy φ = cast_obj D hx hy φ := sorry

/-- Endpoint transport is injective. -/
theorem cast_obj_injective {X Y : C} {f : X ⟶ Y}
    {x x' : D.obj X} {y y' : D.obj Y} (hx : x = x') (hy : y = y') :
    Function.Injective
      (cast_obj D (f := f) (x := x) (x' := x') (y := y) (y' := y') hx hy) := sorry

/-- Equality after endpoint transport is equivalent to equality before transport. -/
@[simp]
theorem cast_obj_eq_iff {X Y : C} {f : X ⟶ Y}
    {x x' : D.obj X} {y y' : D.obj Y} (hx : x = x') (hy : y = y')
    (φ ψ : D.Hom f x y) :
    cast_obj D hx hy φ = cast_obj D hx hy ψ ↔ φ = ψ := sorry

end Hom

end CategoryTheory.DisplayedCategory
