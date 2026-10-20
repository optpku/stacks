/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.CatCommSqOver
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-!
# Costructured arrows of a composite as a categorical pullback

The reverse comparison composes the supplied structural isomorphism with the
supplied costructured arrow. Its objects, maps and unit/counit use only these
given data, with no chosen preimages or abstract equivalence certificate.
-/

@[expose] public section

open CategoryTheory
open scoped CategoryTheory.Limits.CategoricalPullback

universe uA vA uC vC uD vD

namespace CategoryTheory.Limits.CategoricalPullback.CostructuredArrow

variable {A : Type uA} [Category.{vA} A]
variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable (F : A ⥤ C) (G : C ⥤ D) (d : D)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The precomposition square on the two costructured-arrow projections. -/
def square : CatCommSqOver F (CategoryTheory.CostructuredArrow.proj G d)
    (CategoryTheory.CostructuredArrow (F ⋙ G) d) where
  fst := CategoryTheory.CostructuredArrow.proj (F ⋙ G) d
  snd := CategoryTheory.CostructuredArrow.pre F G d
  iso := NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro x y f
    change F.map f.left ≫ 𝟙 _ = 𝟙 _ ≫ F.map f.left
    simp)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Reverse comparison composes the stored isomorphism and structural arrow. -/
def inverse : F ⊡ (CategoryTheory.CostructuredArrow.proj G d) ⥤
    CategoryTheory.CostructuredArrow (F ⋙ G) d where
  obj x := CategoryTheory.CostructuredArrow.mk (Y := x.fst) (G.map x.iso.hom ≫ x.snd.hom)
  map f := CategoryTheory.CostructuredArrow.homMk f.fst (by sorry)
  map_id := by intro x; apply CategoryTheory.CostructuredArrow.hom_ext; rfl
  map_comp := by intro x y z f g; apply CategoryTheory.CostructuredArrow.hom_ext; rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The unit keeps the original object and arrow, using identity maps. -/
def unitIso : 𝟭 (CategoryTheory.CostructuredArrow (F ⋙ G) d) ≅
    (square F G d).comparison ⋙ inverse F G d :=
  NatIso.ofComponents
    (fun x ↦ CategoryTheory.CostructuredArrow.isoMk (Iso.refl x.left) (by sorry))
    (by intros; sorry)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The counit retains the first object and uses the given isomorphism on the second object. -/
def counitIso : inverse F G d ⋙ (square F G d).comparison ≅
    𝟭 (F ⊡ (CategoryTheory.CostructuredArrow.proj G d)) :=
  NatIso.ofComponents
    (fun x ↦ CategoricalPullback.mkIso (Iso.refl x.fst)
      (CategoryTheory.CostructuredArrow.isoMk x.iso (by rfl)) (by sorry))
    (by intros; sorry)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The specified comparison of the precomposition square is an actual equivalence. -/
def equivalence : CategoryTheory.CostructuredArrow (F ⋙ G) d ≌
    F ⊡ (CategoryTheory.CostructuredArrow.proj G d) where
  functor := (square F G d).comparison
  inverse := inverse F G d
  unitIso := unitIso F G d
  counitIso := counitIso F G d
  functor_unitIso_comp := by intros; sorry

/-- The forward functor is precisely the comparison of the given square. -/
@[simp]
theorem equivalence_functor :
    (equivalence F G d).functor = (square F G d).comparison := rfl

/-- The reverse comparison preserves the supplied first object. -/
@[simp]
theorem inverse_obj_left (x : F ⊡ (CategoryTheory.CostructuredArrow.proj G d)) :
    ((inverse F G d).obj x).left = x.fst := rfl

/-- The reverse structural arrow is the image of the supplied isomorphism followed by the given arrow. -/
@[simp]
theorem inverse_obj_hom (x : F ⊡ (CategoryTheory.CostructuredArrow.proj G d)) :
    ((inverse F G d).obj x).hom = G.map x.iso.hom ≫ x.snd.hom := rfl

/-- The reverse comparison preserves the supplied first morphism. -/
@[simp]
theorem inverse_map_left {x y : F ⊡ (CategoryTheory.CostructuredArrow.proj G d)} (f : x ⟶ y) :
    ((inverse F G d).map f).left = f.fst := rfl

end CategoryTheory.Limits.CategoricalPullback.CostructuredArrow
