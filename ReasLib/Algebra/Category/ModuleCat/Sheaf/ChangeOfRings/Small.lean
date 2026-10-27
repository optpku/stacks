/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Sites.Equivalence

/-!
# Module sheaf adjunctions on universe-bounded sites

Transport Mathlib's pullback and sheafification on small models of the sites.
All existence certificates used to choose the resulting left adjoints are proved.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v u' v' w

namespace SheafOfModules

section Reindex

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (J : GrothendieckTopology C) (e : C ≌ D)

set_option backward.isDefEq.respectTransparency false in
/-- Reuse Mathlib's module-pushforward equivalence for a change of site model. -/
private def reindexEquivalence (R : Sheaf J RingCat.{w}) :
    SheafOfModules.{w} R ≌
      SheafOfModules.{w}
        ((e.inverse.sheafPushforwardContinuous RingCat.{w}
          (e.inverse.inducedTopology J) J).obj R) := by
  let K := e.inverse.inducedTopology J
  letI : e.symm.functor.IsContinuous K J :=
    inferInstanceAs (e.inverse.IsContinuous K J)
  letI : e.symm.inverse.IsContinuous J K :=
    inferInstanceAs (e.functor.IsContinuous J K)
  let T := (e.inverse.sheafPushforwardContinuous RingCat.{w} K J).obj R
  let ψ : R ⟶ (e.functor.sheafPushforwardContinuous RingCat.{w} J K).obj T :=
    ((e.sheafCongr J K RingCat.{w}).unitIso.app R).hom
  refine SheafOfModules.pushforwardPushforwardEquivalence
    (J := K) (K := J) (S := T) (R := R) e.symm (𝟙 T) ψ ?_ ?_
  · ext U : 2
    change R.obj.map (e.unitIso.inv.app U.unop).op =
      R.obj.map (e.unitIso.inv.app U.unop).op ≫ 𝟙 _
    rw [Category.comp_id]
  · ext U : 2
    change 𝟙 _ ≫ R.obj.map (e.unitInv.app (e.inverse.obj U.unop)).op ≫
      R.obj.map (e.inverse.map (e.counitInv.app U.unop)).op = 𝟙 _
    rw [Category.id_comp, ← R.obj.map_comp]
    change R.obj.map
      (e.inverse.map (e.counitInv.app U.unop) ≫
        e.unitInv.app (e.inverse.obj U.unop)).op = 𝟙 _
    exact (congrArg (fun f ↦ R.obj.map f.op)
      (e.inverse_counitInv_comp U.unop)).trans (R.obj.map_id _)


end Reindex

set_option backward.isDefEq.respectTransparency false in
/-- Continuous pushforward of module sheaves on essentially small sites admits a left adjoint.
The witness is transported from Mathlib's presheaf pullback followed by sheafification. -/
theorem pushforward_isRightAdjoint_of_essentiallySmall
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F : C ⥤ D} [F.IsContinuous J K]
    {S : Sheaf J RingCat.{w}} {R : Sheaf K RingCat.{w}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{w} J K).obj R) :
    (SheafOfModules.pushforward.{w} φ).IsRightAdjoint := by
  let c := equivSmallModel.{w} C
  let d := equivSmallModel.{w} D
  let J₀ := c.inverse.inducedTopology J
  let K₀ := d.inverse.inducedTopology K
  let S₀ := (c.inverse.sheafPushforwardContinuous RingCat.{w} J₀ J).obj S
  let R₀ := (d.inverse.sheafPushforwardContinuous RingCat.{w} K₀ K).obj R
  let ψ : R ⟶ (d.functor.sheafPushforwardContinuous RingCat.{w} K K₀).obj R₀ :=
    ((d.sheafCongr K K₀ RingCat.{w}).unitIso.app R).hom
  letI : (F ⋙ d.functor).IsContinuous J K₀ :=
    Functor.isContinuous_comp F d.functor J K K₀
  let H := c.inverse ⋙ F ⋙ d.functor
  letI : H.IsContinuous J₀ K₀ :=
    Functor.isContinuous_comp c.inverse (F ⋙ d.functor) J₀ J K₀
  let φ₀ : S₀ ⟶ (H.sheafPushforwardContinuous RingCat.{w} J₀ K₀).obj R₀ :=
    (c.inverse.sheafPushforwardContinuous RingCat.{w} J₀ J).map
      (φ ≫ (F.sheafPushforwardContinuous RingCat.{w} J K).map ψ)
  let E := reindexEquivalence J c S
  let E' := reindexEquivalence K d R
  let comparison :
      (E'.inverse ⋙ SheafOfModules.pushforward.{w} φ) ⋙ E.functor ≅
        SheafOfModules.pushforward.{w} φ₀ := by
    exact Iso.refl _
  letI : (SheafOfModules.pushforward.{w} φ₀).IsRightAdjoint := inferInstance
  letI : ((E'.inverse ⋙ SheafOfModules.pushforward.{w} φ) ⋙ E.functor).IsRightAdjoint :=
    Functor.isRightAdjoint_of_iso comparison.symm
  letI : (E'.inverse ⋙ SheafOfModules.pushforward.{w} φ).IsRightAdjoint :=
    (Functor.isRightAdjoint_comp_iff_left _ E.functor).mp inferInstance
  exact (Functor.isRightAdjoint_comp_iff_right E'.inverse _).mp inferInstance


/-- A bound on objects and arrows supplies Mathlib's canonical small model. -/
private theorem essentiallySmall_of_univLE
    (C : Type u) [Category.{v} C] [UnivLE.{max u v, w}] :
    EssentiallySmall.{w} C := by
  letI : Small.{w} C :=
    @Small.trans_univLE.{max u v, w, u} C (small_max.{v} C) inferInstance
  letI : LocallySmall.{w} C :=
    ⟨fun U V ↦ @Small.trans_univLE.{max u v, w, v} (U ⟶ V)
      (small_max.{u} (U ⟶ V)) inferInstance⟩
  exact essentiallySmall_of_small_of_locallySmall C

/-- Continuous pushforward of module sheaves is a right adjoint when both sites fit in
 the coefficient universe. -/
theorem pushforward_isRightAdjoint_of_univLE
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    [UnivLE.{max u v, w}] [UnivLE.{max u' v', w}]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F : C ⥤ D} [F.IsContinuous J K]
    {S : Sheaf J RingCat.{w}} {R : Sheaf K RingCat.{w}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{w} J K).obj R) :
    (SheafOfModules.pushforward.{w} φ).IsRightAdjoint := by
  letI : EssentiallySmall.{w} C := essentiallySmall_of_univLE C
  letI : EssentiallySmall.{w} D := essentiallySmall_of_univLE D
  exact pushforward_isRightAdjoint_of_essentiallySmall φ

namespace ChangeOfRings

/-- Restriction of scalars between sheaves of modules on a site bounded by the
coefficient universe admits a left adjoint. -/
instance restrictScalars_isRightAdjoint_of_univLE
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [UnivLE.{max u v, w}] {R S : Sheaf J RingCat.{w}} (α : R ⟶ S) :
    (SheafOfModules.restrictScalars.{w} α).IsRightAdjoint := by
  letI : (SheafOfModules.pushforward.{w} (homOverId α)).IsRightAdjoint :=
    pushforward_isRightAdjoint_of_univLE (homOverId α)
  exact Functor.isRightAdjoint_of_iso (pushforwardIso α)

end ChangeOfRings

end SheafOfModules
