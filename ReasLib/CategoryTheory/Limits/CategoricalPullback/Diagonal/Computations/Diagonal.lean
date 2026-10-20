/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Diagonal.Basic
public import Mathlib.CategoryTheory.EqToHom

/-!
# Readouts for the relative diagonal

This leaf contains the object, morphism, comparison-map, and projection-isomorphism computations
for `CategoricalPullback.diagonal`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open scoped CategoricalPullback

namespace CategoryTheory.Limits.CategoricalPullback.diagonal

universe vC vD uC uD

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]

/-- The first endpoint of `Δₚ H` is the input object itself. -/
@[simp] theorem obj.fst (H : C ⥤ D) (X : C) :
    ((Δₚ H).obj X).fst = X := sorry

/-- The second endpoint of `Δₚ H` is the input object itself. -/
@[simp] theorem obj.snd (H : C ⥤ D) (X : C) :
    ((Δₚ H).obj X).snd = X := sorry

/-- The two endpoint images of the comparison carried by `Δₚ H` are equal. -/
theorem obj.fstImage_eq_sndImage (H : C ⥤ D) (X : C) :
    H.obj ((Δₚ H).obj X).fst = H.obj ((Δₚ H).obj X).snd := sorry

/-- The comparison isomorphism carried by an object of `Δₚ H` is the equality isomorphism. -/
@[simp] theorem obj.iso (H : C ⥤ D) (X : C) :
    ((Δₚ H).obj X).iso = eqToIso (obj.fstImage_eq_sndImage H X) := sorry

/-- The forward comparison map carried by an object of `Δₚ H`. -/
@[simp] theorem obj.iso.hom (H : C ⥤ D) (X : C) :
    ((Δₚ H).obj X).iso.hom = eqToHom (obj.fstImage_eq_sndImage H X) := sorry

/-- The inverse comparison map carried by an object of `Δₚ H`. -/
@[simp] theorem obj.iso.inv (H : C ⥤ D) (X : C) :
    ((Δₚ H).obj X).iso.inv = eqToHom (obj.fstImage_eq_sndImage H X).symm := sorry

/-- The first morphism component of `Δₚ H` is the supplied morphism. -/
@[simp] theorem map.fst (H : C ⥤ D) {X Y : C} (f : X ⟶ Y) :
    ((Δₚ H).map f).fst = f := sorry

/-- The second morphism component of `Δₚ H` is the supplied morphism. -/
@[simp] theorem map.snd (H : C ⥤ D) {X Y : C} (f : X ⟶ Y) :
    ((Δₚ H).map f).snd = f := sorry

/-- Naturality of the structural comparison of `Δₚ H` in the forward direction. -/
@[reassoc] theorem map.naturality (H : C ⥤ D) {X Y : C} (f : X ⟶ Y) :
    H.map ((Δₚ H).map f).fst ≫ ((Δₚ H).obj Y).iso.hom =
      ((Δₚ H).obj X).iso.hom ≫ H.map ((Δₚ H).map f).snd := sorry

/-- Naturality of the structural comparison of `Δₚ H` in the inverse direction. -/
@[reassoc] theorem map.invNaturality (H : C ⥤ D) {X Y : C} (f : X ⟶ Y) :
    H.map ((Δₚ H).map f).snd ≫ ((Δₚ H).obj Y).iso.inv =
      ((Δₚ H).obj X).iso.inv ≫ H.map ((Δₚ H).map f).fst := sorry

/-- The first projection of `Δₚ H` is canonically the identity functor. -/
def fstIso (H : C ⥤ D) : Δₚ H ⋙ π₁ H H ≅ 𝟭 C := Iso.refl _

/-- The second projection of `Δₚ H` is canonically the identity functor. -/
def sndIso (H : C ⥤ D) : Δₚ H ⋙ π₂ H H ≅ 𝟭 C := Iso.refl _

/-- The forward component of the first projection comparison. -/
@[simp] theorem fstIso.hom.app (H : C ⥤ D) (X : C) :
    (fstIso H).hom.app X = 𝟙 X := sorry

/-- The inverse component of the first projection comparison. -/
@[simp] theorem fstIso.inv.app (H : C ⥤ D) (X : C) :
    (fstIso H).inv.app X = 𝟙 X := sorry

/-- The forward component of the second projection comparison. -/
@[simp] theorem sndIso.hom.app (H : C ⥤ D) (X : C) :
    (sndIso H).hom.app X = 𝟙 X := sorry

/-- The inverse component of the second projection comparison. -/
@[simp] theorem sndIso.inv.app (H : C ⥤ D) (X : C) :
    (sndIso H).inv.app X = 𝟙 X := sorry

end CategoryTheory.Limits.CategoricalPullback.diagonal
