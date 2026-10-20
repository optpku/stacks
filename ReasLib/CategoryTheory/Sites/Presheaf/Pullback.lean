/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Presheaf.InverseImage
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction

/-!
# Pullback maps of presheaves

Right Kan extensions along a composable triangle of functors induce the
pushforward comparison and the unit-induced pullback map for presheaves.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v u' v' u'' v'' w

namespace CategoryTheory.Functor

variable {V : Type u} [Category.{v} V]
variable {U : Type u'} [Category.{v'} U]
variable {X : Type u''} [Category.{v''} X]
variable {A : Type w} [Category A]

/-- The pushforward comparison for a triangle `h ⋙ f ≅ g` of functors. -/
def presheafPushforwardCompIso
    (h : V ⥤ U) (f : U ⥤ X) {g : V ⥤ X} (e : h ⋙ f ≅ g)
    [∀ F : Vᵒᵖ ⥤ A, HasRightKanExtension h.op F]
    [∀ F : Uᵒᵖ ⥤ A, HasRightKanExtension f.op F]
    [∀ F : Vᵒᵖ ⥤ A, HasRightKanExtension g.op F] :
    (g.op.ran : (Vᵒᵖ ⥤ A) ⥤ (Xᵒᵖ ⥤ A)) ≅
      (h.op.ran : (Vᵒᵖ ⥤ A) ⥤ (Uᵒᵖ ⥤ A)) ⋙
        (f.op.ran : (Uᵒᵖ ⥤ A) ⥤ (Xᵒᵖ ⥤ A)) := by
  let leftIso :
      (whiskeringLeft Vᵒᵖ Xᵒᵖ A).obj g.op ≅
        (whiskeringLeft Uᵒᵖ Xᵒᵖ A).obj f.op ⋙
          (whiskeringLeft Vᵒᵖ Uᵒᵖ A).obj h.op := by
    simpa only [whiskeringLeft_obj_comp] using
      (whiskeringLeft Vᵒᵖ Xᵒᵖ A).mapIso (NatIso.op e ≪≫ opComp h f)
  exact (g.op.ranAdjunction A).ofNatIsoLeft leftIso |>.rightAdjointUniq
    ((f.op.ranAdjunction A).comp (h.op.ranAdjunction A))

/-- The map from the pushforward along `f` to the pushforward along `g` after
pulling back along `h`, obtained from the unit of the right Kan extension
adjunction for `h`. -/
def presheafPullbackMap
    (h : V ⥤ U) (f : U ⥤ X) {g : V ⥤ X} (e : h ⋙ f ≅ g)
    [∀ F : Vᵒᵖ ⥤ A, HasRightKanExtension h.op F]
    [∀ F : Uᵒᵖ ⥤ A, HasRightKanExtension f.op F]
    [∀ F : Vᵒᵖ ⥤ A, HasRightKanExtension g.op F] :
    (f.op.ran : (Uᵒᵖ ⥤ A) ⥤ (Xᵒᵖ ⥤ A)) ⟶
      presheafInverseImage h A ⋙
        (g.op.ran : (Vᵒᵖ ⥤ A) ⥤ (Xᵒᵖ ⥤ A)) :=
  whiskerRight (h.op.ranAdjunction A).unit f.op.ran ≫
    whiskerLeft (presheafInverseImage h A)
      (presheafPushforwardCompIso h f e).inv

/-- The component of `presheafPullbackMap` at a presheaf `G` is the direct
image of the adjunction unit followed by the inverse pushforward comparison. -/
theorem presheafPullbackMap_app
    (h : V ⥤ U) (f : U ⥤ X) {g : V ⥤ X} (e : h ⋙ f ≅ g)
    [∀ F : Vᵒᵖ ⥤ A, HasRightKanExtension h.op F]
    [∀ F : Uᵒᵖ ⥤ A, HasRightKanExtension f.op F]
    [∀ F : Vᵒᵖ ⥤ A, HasRightKanExtension g.op F]
    (G : Uᵒᵖ ⥤ A) :
    (presheafPullbackMap h f e).app G =
      f.op.ran.map ((h.op.ranAdjunction A).unit.app G) ≫
        (presheafPushforwardCompIso h f e).inv.app
          ((presheafInverseImage h A).obj G) := sorry

end CategoryTheory.Functor

end
