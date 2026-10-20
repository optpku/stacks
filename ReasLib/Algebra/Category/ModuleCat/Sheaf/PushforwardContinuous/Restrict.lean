/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Direct image and restriction of scalars

This leaf owns the two canonical comparisons between direct image and restriction of scalars.
It identifies a direct image followed by a same-site restriction with the direct image for the
composite ring map, and identifies restriction on the source of direct image with postcomposition
of its coefficient map.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w u' v'

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable {F : C ⥤ D} [F.IsContinuous J K]
variable {S T : Sheaf J RingCat.{w}} {R R' : Sheaf K RingCat.{w}}

/-- A module direct image followed by restriction of scalars is canonically the module direct
image along the composite ring-sheaf morphism. -/
@[stacks 03D8 "pushforward after restriction of scalars"]
noncomputable def pushforwardRestrictIso (α : S ⟶ T)
    (ψ : T ⟶ (F.sheafPushforwardContinuous RingCat.{w} J K).obj R) :
    pushforward ψ ⋙ restrictScalars α ≅
      pushforward
        (ChangeOfRings.homOverId α ≫
          ((𝟭 C).sheafPushforwardContinuous RingCat.{w} J J).map ψ) :=
  (pushforward ψ).isoWhiskerLeft (ChangeOfRings.pushforwardIso α).symm ≪≫
    pushforwardComp (ChangeOfRings.homOverId α) ψ

/-- The identity-site presentation of restriction of scalars is compatible with the right
unitor for continuous direct image. -/
theorem restrictPushforward_rightUnitor (α : R ⟶ R')
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{w} J K).obj R)
    (φ' : S ⟶ (F.sheafPushforwardContinuous RingCat.{w} J K).obj R')
    (h : φ ≫ (F.sheafPushforwardContinuous RingCat.{w} J K).map α = φ') :
    (φ ≫ (F.sheafPushforwardContinuous RingCat.{w} J K).map
        (ChangeOfRings.homOverId α)) ≫
      (Functor.sheafPushforwardContinuousNatTrans
        (Functor.rightUnitor F).inv _ _ _).app R' = φ' := sorry

/-- Restricting scalars before a module direct image is canonically the direct image obtained by
postcomposing its coefficient map. -/
noncomputable def restrictPushforwardIso (α : R ⟶ R')
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{w} J K).obj R)
    (φ' : S ⟶ (F.sheafPushforwardContinuous RingCat.{w} J K).obj R')
    (h : φ ≫ (F.sheafPushforwardContinuous RingCat.{w} J K).map α = φ') :
    restrictScalars α ⋙ pushforward φ ≅ pushforward φ' :=
  Functor.isoWhiskerRight (ChangeOfRings.pushforwardIso α).symm (pushforward φ) ≪≫
    pushforwardComp φ (ChangeOfRings.homOverId α) ≪≫
    pushforwardCongr₂
      (φ ≫ (F.sheafPushforwardContinuous RingCat.{w} J K).map
        (ChangeOfRings.homOverId α))
      (Functor.rightUnitor F).symm
      (restrictPushforward_rightUnitor α φ φ' h)

end SheafOfModules
