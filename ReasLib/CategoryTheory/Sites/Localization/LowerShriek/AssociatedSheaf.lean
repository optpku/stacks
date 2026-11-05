/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

universe w v u

noncomputable section

variable {C : Type u} [Category.{v} C] [h_locallySmall : LocallySmall.{w} C]

include h_locallySmall

/-- Left Kan extension along `(Over.forget U).op` sends the slice-site sheafification unit to a
map inverted by sheafification on the ambient site. -/
noncomputable instance localization_lowerShriek_toSheafify_map_isIso
    (J : GrothendieckTopology C) (U : C) (G : (Over U)ᵒᵖ ⥤ Type w)
    [∀ F : (Over U)ᵒᵖ ⥤ Type w, (Over.forget U).op.HasLeftKanExtension F]
    [HasWeakSheafify (J.over U) (Type w)]
    [HasWeakSheafify J (Type w)] :
    IsIso ((presheafToSheaf J (Type w)).map
      (((Over.forget U).op.lan).map (toSheafify (J.over U) G))) := by
  exact (sheafificationAdjunction (J.over U) (Type w)).isIso_map_unit_of_isLeftAdjoint_comp
    (S := (Over.forget U).sheafPushforwardContinuous (Type w) (J.over U) J)
    (((Over.forget U).op.lanAdjunction (Type w)).comp
      (sheafificationAdjunction J (Type w)))

attribute [-instance]
  localization_lowerShriek_toSheafify_map_isIso

/-- Lemma 7.25.2 (03CD): applying localization lower shriek to the sheafification of `G` is
canonically isomorphic to sheafifying the left Kan extension of `G` along `(Over.forget U).op`. -/
@[stacks 03CD]
noncomputable def localization_lowerShriek_associatedSheafIso
    (J : GrothendieckTopology C) (U : C) (G : (Over U)ᵒᵖ ⥤ Type w)
    [∀ F : (Over U)ᵒᵖ ⥤ Type w, (Over.forget U).op.HasLeftKanExtension F]
    [HasWeakSheafify (J.over U) (Type w)]
    [HasWeakSheafify J (Type w)] :
    ((Over.forget U).sheafPullback (Type w) (J.over U) J).obj
      ((presheafToSheaf (J.over U) (Type w)).obj G) ≅
      (presheafToSheaf J (Type w)).obj ((Over.forget U).op.lan.obj G) :=
  let η := ((Over.forget U).op.lan).map (toSheafify (J.over U) G)
  letI : IsIso ((presheafToSheaf J (Type w)).map η) :=
    localization_lowerShriek_toSheafify_map_isIso J U G
  (sheafPullbackIso (Over.forget U) (Type w) (J.over U) J).app
      ((presheafToSheaf (J.over U) (Type w)).obj G) ≪≫
    eqToIso rfl ≪≫
    (asIso ((presheafToSheaf J (Type w)).map η)).symm
