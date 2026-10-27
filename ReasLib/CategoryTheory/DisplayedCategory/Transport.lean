/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DisplayedCategory.Structure
public import ReasLib.CategoryTheory.DisplayedCategory.Transport.Endpoint

/-!
# Equality transport for displayed morphisms

Displayed morphisms are indexed by their base morphism.  This leaf gives the canonical equality
transport for that index and the small API needed to compose, invert, and compare transports.
The definitions deliberately reduce to Lean's primitive `Eq.rec` transport, so adapters whose
owners already use `h ▸ m` remain definitionally aligned with this API.
-/

@[expose] public section

universe v u w₁ w₂

namespace CategoryTheory.DisplayedCategory

variable {C : Type u} [Category.{v} C]
variable (D : DisplayedCategory C)

namespace Obj

/-- Transport a displayed object along an equality of its underlying base objects. -/
def cast {X Y : C} (h : X = Y) (x : D.obj X) : D.obj Y :=
  h ▸ x

/-- Transport along reflexivity leaves a displayed object unchanged. -/
@[simp]
theorem cast_rfl {X : C} (x : D.obj X) : Obj.cast D rfl x = x := rfl

/-- Successive displayed-object transports combine by transitivity of equality. -/
theorem cast_trans {X Y Z : C} (p : X = Y) (q : Y = Z) (x : D.obj X) :
    Obj.cast D q (Obj.cast D p x) = Obj.cast D (p.trans q) x := by
  cases p
  cases q
  rfl

/-- Transporting a displayed object forward and then back recovers it. -/
@[simp]
theorem cast_symm_apply {X Y : C} (p : X = Y) (x : D.obj X) :
    Obj.cast D p.symm (Obj.cast D p x) = x := by
  cases p
  rfl

/-- Transporting a displayed object backward and then forward recovers it. -/
@[simp]
theorem cast_apply_symm {X Y : C} (p : X = Y) (x : D.obj Y) :
    Obj.cast D p (Obj.cast D p.symm x) = x := by
  cases p
  rfl

/-- The equivalence between displayed-object fibers induced by an equality of base objects. -/
def castEquiv {X Y : C} (p : X = Y) : D.obj X ≃ D.obj Y where
  toFun := Obj.cast D p
  invFun := Obj.cast D p.symm
  left_inv := Obj.cast_symm_apply D p
  right_inv := Obj.cast_apply_symm D p

/-- Applying `castEquiv` is the canonical displayed-object transport. -/
@[simp]
theorem castEquiv_apply {X Y : C} (p : X = Y) (x : D.obj X) :
    Obj.castEquiv D p x = Obj.cast D p x := rfl

/-- Applying the inverse of `castEquiv` is transport along the reverse equality. -/
@[simp]
theorem castEquiv_symm_apply {X Y : C} (p : X = Y) (x : D.obj Y) :
    (Obj.castEquiv D p).symm x = Obj.cast D p.symm x := rfl

/-- Equality transport is injective on every displayed-object fiber. -/
theorem cast_injective {X Y : C} (p : X = Y) :
    Function.Injective (Obj.cast D p) :=
  (Obj.castEquiv D p).injective

/-- Two displayed objects are equal after the same base transport exactly when they were equal
before transport. -/
@[simp]
theorem cast_eq_iff {X Y : C} (p : X = Y) (x y : D.obj X) :
    Obj.cast D p x = Obj.cast D p y ↔ x = y :=
  (Obj.cast_injective D p).eq_iff

end Obj

namespace Hom

/-- Transport a displayed morphism along an equality of its underlying base morphisms. -/
def cast {X Y : C} {f g : X ⟶ Y} {x : D.obj X} {y : D.obj Y}
    (h : f = g) (φ : D.Hom f x y) : D.Hom g x y :=
  h ▸ φ

/-- Transport along reflexivity leaves a displayed morphism unchanged. -/
@[simp]
theorem cast_rfl {X Y : C} {f : X ⟶ Y} {x : D.obj X} {y : D.obj Y}
    (φ : D.Hom f x y) : DisplayedCategory.Hom.cast D rfl φ = φ := rfl

/-- Successive displayed-morphism transports combine by transitivity of equality. -/
theorem cast_trans {X Y : C} {f g h : X ⟶ Y} {x : D.obj X} {y : D.obj Y}
    (p : f = g) (q : g = h) (φ : D.Hom f x y) :
    DisplayedCategory.Hom.cast D q (DisplayedCategory.Hom.cast D p φ) =
      DisplayedCategory.Hom.cast D (p.trans q) φ := by
  cases p
  cases q
  rfl

/-- Transporting a displayed morphism forward and then back recovers it. -/
@[simp]
theorem cast_symm_apply {X Y : C} {f g : X ⟶ Y} {x : D.obj X} {y : D.obj Y}
    (p : f = g) (φ : D.Hom f x y) :
    DisplayedCategory.Hom.cast D p.symm (DisplayedCategory.Hom.cast D p φ) = φ := by
  cases p
  rfl

/-- Transporting a displayed morphism backward and then forward recovers it. -/
@[simp]
theorem cast_apply_symm {X Y : C} {f g : X ⟶ Y} {x : D.obj X} {y : D.obj Y}
    (p : f = g) (φ : D.Hom g x y) :
    DisplayedCategory.Hom.cast D p (DisplayedCategory.Hom.cast D p.symm φ) = φ := by
  cases p
  rfl

/-- The equivalence between displayed hom types induced by an equality of base morphisms. -/
def castEquiv {X Y : C} {f g : X ⟶ Y} {x : D.obj X} {y : D.obj Y}
    (p : f = g) : D.Hom f x y ≃ D.Hom g x y where
  toFun := fun φ => DisplayedCategory.Hom.cast D p φ
  invFun := fun φ => DisplayedCategory.Hom.cast D p.symm φ
  left_inv := fun φ => DisplayedCategory.Hom.cast_symm_apply D p φ
  right_inv := fun φ => DisplayedCategory.Hom.cast_apply_symm D p φ

/-- Applying `castEquiv` is the canonical displayed-morphism transport. -/
@[simp]
theorem castEquiv_apply {X Y : C} {f g : X ⟶ Y} {x : D.obj X} {y : D.obj Y}
    (p : f = g) (φ : D.Hom f x y) :
    DisplayedCategory.Hom.castEquiv D p φ = DisplayedCategory.Hom.cast D p φ := rfl

/-- Applying the inverse of `castEquiv` is transport along the reverse equality. -/
@[simp]
theorem castEquiv_symm_apply {X Y : C} {f g : X ⟶ Y} {x : D.obj X} {y : D.obj Y}
    (p : f = g) (φ : D.Hom g x y) :
    (DisplayedCategory.Hom.castEquiv D p).symm φ =
      DisplayedCategory.Hom.cast D p.symm φ := rfl

/-- Equality transport is injective on every displayed hom type. -/
theorem cast_injective {X Y : C} {f g : X ⟶ Y} {x : D.obj X} {y : D.obj Y}
    (p : f = g) :
    Function.Injective (DisplayedCategory.Hom.cast D (x := x) (y := y) p) :=
  (DisplayedCategory.Hom.castEquiv D (x := x) (y := y) p).injective

/-- Two displayed morphisms are equal after the same base transport exactly when they were equal
before transport. -/
@[simp]
theorem cast_eq_iff {X Y : C} {f g : X ⟶ Y} {x : D.obj X} {y : D.obj Y}
    (p : f = g) (φ ψ : D.Hom f x y) :
    DisplayedCategory.Hom.cast D p φ = DisplayedCategory.Hom.cast D p ψ ↔ φ = ψ :=
  (DisplayedCategory.Hom.cast_injective D p).eq_iff

/-- A transported displayed morphism can be compared with a morphism in the target fiber by
transporting the latter back. -/
theorem cast_eq_iff_target {X Y : C} {f g : X ⟶ Y} {x : D.obj X} {y : D.obj Y}
    (p : f = g) (φ : D.Hom f x y) (ψ : D.Hom g x y) :
    DisplayedCategory.Hom.cast D p φ = ψ ↔
      φ = DisplayedCategory.Hom.cast D p.symm ψ := by
  cases p
  rfl

/-- The displayed left-identity law in canonical transport form. -/
@[simp]
theorem id_comp {X Y : C} {f : X ⟶ Y} {x : D.obj X} {y : D.obj Y}
    (φ : D.Hom f x y) :
    DisplayedCategory.Hom.cast D (Category.id_comp f) (D.comp (D.id x) φ) = φ :=
  D.id_comp φ

/-- The displayed right-identity law in canonical transport form. -/
@[simp]
theorem comp_id {X Y : C} {f : X ⟶ Y} {x : D.obj X} {y : D.obj Y}
    (φ : D.Hom f x y) :
    DisplayedCategory.Hom.cast D (Category.comp_id f) (D.comp φ (D.id y)) = φ :=
  D.comp_id φ

/-- Displayed composition is associative after canonical base-morphism transport. -/
@[simp]
theorem assoc {W X Y Z : C} {f : W ⟶ X} {g : X ⟶ Y} {h : Y ⟶ Z}
    {w : D.obj W} {x : D.obj X} {y : D.obj Y} {z : D.obj Z}
    (φ : D.Hom f w x) (ψ : D.Hom g x y) (χ : D.Hom h y z) :
    DisplayedCategory.Hom.cast D (Category.assoc f g h)
        (D.comp (D.comp φ ψ) χ) =
      D.comp φ (D.comp ψ χ) :=
  D.assoc φ ψ χ

/-- Transport in the left factor commutes with displayed composition. -/
@[simp]
theorem cast_comp_left {X Y Z : C} {f f' : X ⟶ Y} {g : Y ⟶ Z}
    {x : D.obj X} {y : D.obj Y} {z : D.obj Z}
    (p : f = f') (φ : D.Hom f x y) (ψ : D.Hom g y z) :
    DisplayedCategory.Hom.cast D
        (congrArg (fun a : X ⟶ Y => a ≫ g) p) (D.comp φ ψ) =
      D.comp (DisplayedCategory.Hom.cast D p φ) ψ := by
  cases p
  rfl

/-- Transport in the right factor commutes with displayed composition. -/
@[simp]
theorem cast_comp_right {X Y Z : C} {f : X ⟶ Y} {g g' : Y ⟶ Z}
    {x : D.obj X} {y : D.obj Y} {z : D.obj Z}
    (q : g = g') (φ : D.Hom f x y) (ψ : D.Hom g y z) :
    DisplayedCategory.Hom.cast D
        (congrArg (fun b : Y ⟶ Z => f ≫ b) q) (D.comp φ ψ) =
      D.comp φ (DisplayedCategory.Hom.cast D q ψ) := by
  cases q
  rfl

/-- Transport commutes with displayed composition when both underlying base morphisms are
transported simultaneously. -/
@[simp]
theorem cast_comp {X Y Z : C} {f f' : X ⟶ Y} {g g' : Y ⟶ Z}
    {x : D.obj X} {y : D.obj Y} {z : D.obj Z}
    (p : f = f') (q : g = g') (φ : D.Hom f x y) (ψ : D.Hom g y z) :
    DisplayedCategory.Hom.cast D
        (congrArg₂ (fun (a : X ⟶ Y) (b : Y ⟶ Z) => a ≫ b) p q)
        (D.comp φ ψ) =
      D.comp (DisplayedCategory.Hom.cast D p φ) (DisplayedCategory.Hom.cast D q ψ) := by
  cases p
  cases q
  rfl

end Hom

end CategoryTheory.DisplayedCategory
