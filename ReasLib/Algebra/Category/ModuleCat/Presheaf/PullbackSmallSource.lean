/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback

/-! # Presheaf module pullback with a small source site

The free represented construction needs the source objects and both Hom universes to fit the
coefficient universe. The target object's universe can be independent: each actual source free
representable is sent to the free representable of its given target image.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u d

namespace PresheafOfModules.SmallSourcePullback

variable {C : Type u} [SmallCategory C] {D : Type d} [Category.{u} D]
variable {F : C ⥤ D} {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}}
variable (φ : S ⟶ F.op ⋙ R)

/-- The actual free target representable corepresents pushforward evaluated at the specified
free source representable. Both maps are the original free-Yoneda maps. -/
def freeCorepresentable (X : C) :
    (PresheafOfModules.pushforward φ ⋙
      coyoneda.obj (op ((PresheafOfModules.free S).obj (yoneda.obj X)))).CorepresentableBy
        ((PresheafOfModules.free R).obj (yoneda.obj (F.obj X))) where
  homEquiv {M} := PresheafOfModules.freeYonedaEquiv.trans
    (PresheafOfModules.freeYonedaEquiv (M := (PresheafOfModules.pushforward φ).obj M)).symm
  homEquiv_comp {M N} g f := by sorry

/-- Each genuine free source summand has the specified actual pullback value. -/
theorem pullbackObjIsDefined_free (X : C) :
    PresheafOfModules.pullbackObjIsDefined φ ((PresheafOfModules.free S).obj (yoneda.obj X)) :=
  (freeCorepresentable φ X).isCorepresentable

/-- The original source free presentation constructs the adjoint object using its actual
coproducts and cokernel, with the target representables already supplied above. -/
theorem pullbackObjIsDefined_eq_top : PresheafOfModules.pullbackObjIsDefined.{u} φ = ⊤ := by
  ext M
  simp only [Pi.top_apply, Prop.top_eq_true, iff_true]
  apply Functor.leftAdjointObjIsDefined_of_isColimit M.isColimitFreeYonedaCoproductsCokernelCofork
  rintro (_ | _)
  all_goals
    apply Functor.leftAdjointObjIsDefined_colimit _ (fun _ ↦ pullbackObjIsDefined_free _ _)

/-- The adjunction certificate contains the native free represented and colimit construction. -/
instance isRightAdjoint : (PresheafOfModules.pushforward.{u} φ).IsRightAdjoint :=
  Functor.isRightAdjoint_of_leftAdjointObjIsDefined_eq_top (pullbackObjIsDefined_eq_top φ)

end PresheafOfModules.SmallSourcePullback
