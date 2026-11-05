/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Topos.Continuous
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
public import ReasLib.CategoryTheory.Sites.FullyFaithful
public import Mathlib.CategoryTheory.Sites.Over

/-!
# Retractions from continuous and cocontinuous site functors

This leaf records the topos-level retraction supplied by a fully faithful site
functor that is both continuous and cocontinuous, together with its localized
form on over-categories.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped MorphismOfTopoiIn

noncomputable section

universe w vC vD uC uD vA uA

namespace CategoryTheory.Functor

namespace Retraction

set_option backward.isDefEq.respectTransparency false in
/-- The continuous sheaf adjunction has invertible unit for a fully faithful,
continuous and cocontinuous functor. This follows from the left Kan extension
unit and compatibility of sheafification with continuous pushforward. -/
theorem continuousUnit_isIso
    {C : Type uC} {D : Type uD}
    [Category.{vC} C] [Category.{vD} D]
    (A : Type uA) [Category.{vA} A]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (u : C ⥤ D) [u.Full] [u.Faithful]
    [u.IsContinuous J K] [u.IsCocontinuous J K]
    [HasWeakSheafify J A] [HasWeakSheafify K A]
    [∀ P : Cᵒᵖ ⥤ A, u.op.HasLeftKanExtension P]
    [∀ P : Cᵒᵖ ⥤ A, u.op.HasPointwiseLeftKanExtension P]
    [∀ P : Cᵒᵖ ⥤ A, u.op.HasPointwiseRightKanExtension P] :
    IsIso (u.sheafAdjunctionContinuous A J K).unit := by
  let adj := sheafPullbackConstruction.sheafAdjunctionContinuous u A J K
  have hunit (F : Sheaf J A) : IsIso (adj.unit.app F) := by
    suffices h : IsIso ((sheafToPresheaf J A).map (adj.unit.app F)) by
      letI := h
      exact isIso_of_reflects_iso _ (sheafToPresheaf J A)
    change IsIso ((sheafToPresheaf J A).map
      ((sheafPullbackConstruction.sheafAdjunctionContinuous u A J K).unit.app F))
    rw [sheafPullbackConstruction.sheafAdjunctionContinuous,
      Adjunction.map_restrictFullyFaithful_unit_app]
    simp only [Iso.refl_hom, NatTrans.id_app, Adjunction.comp_unit_app]
    erw [Functor.map_id, Category.comp_id, Category.comp_id]
    rw [Functor.lanAdjunction_unit]
    change IsIso (u.op.lanUnit.app F.obj ≫ whiskerLeft u.op
      (toSheafify K (u.op.lan.obj F.obj)))
    rw [← u.toSheafify_pullbackSheafificationCompatibility A J K,
      ← Category.assoc]
    erw [toSheafify_naturality]
    letI := isIso_toSheafify J F.property
    change IsIso ((toSheafify J F.obj ≫
      (sheafToPresheaf J A).map
        ((presheafToSheaf J A).map (u.op.lanUnit.app F.obj))) ≫
      (sheafToPresheaf J A).map
        ((u.pushforwardContinuousSheafificationCompatibility A J K).hom.app
          (u.op.lan.obj F.obj)))
    infer_instance
  letI : IsIso adj.unit := NatIso.isIso_of_isIso_app _
  rw [← isIso_comp_right_iff _
    (whiskerRight ((u.sheafAdjunctionContinuous A J K).leftAdjointUniq adj).hom
      (u.sheafPushforwardContinuous A J K)),
    Adjunction.unit_leftAdjointUniq_hom]
  infer_instance

/-- The composite inverse image of the continuous and cocontinuous morphisms of topoi attached
to a fully faithful functor of sites is naturally isomorphic to the identity. -/
noncomputable def compInverseImageIso
    {C : Type uC} {D : Type uD}
    [Category.{vC} C] [Category.{vD} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (u : C ⥤ D)
    [u.Full] [u.Faithful]
    [u.IsContinuous J K] [u.IsCocontinuous J K]
    [HasWeakSheafify K (Type w)]
    [∀ P : Cᵒᵖ ⥤ Type w, u.op.HasLeftKanExtension P]
    [∀ P : Cᵒᵖ ⥤ Type w, u.op.HasPointwiseLeftKanExtension P]
    [PreservesFiniteLimits (u.sheafPullback (Type w) J K)]
    [HasSheafify J (Type w)]
    [∀ P : Cᵒᵖ ⥤ Type w, u.op.HasPointwiseRightKanExtension P] :
    (MorphismOfTopoiIn.comp
        (u.morphismOfTopoiInOfContinuous J K)
        (u.morphismOfTopoiInOfCocontinuous J K)).inverseImage ≅
      (MorphismOfTopoiIn.id J).inverseImage :=
  Functor.isoWhiskerLeft (u.sheafPullback (Type w) J K)
      (CocontinuousPullback.comparisonIso.{w} u J K) ≪≫
    (@asIso _ _ _ _ (u.sheafAdjunctionContinuous (Type w) J K).unit
      (continuousUnit_isIso (Type w) J K u)).symm

/-- For a functor induced on over-categories, the composite inverse image of the continuous and
cocontinuous morphisms of topoi is naturally isomorphic to the identity. -/
noncomputable def overCompInverseImageIso
    {C : Type uC} {D : Type uD}
    [Category.{vC} C] [Category.{vD} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (u : C ⥤ D) (X : C)
    [(Over.post (X := X) u).Full]
    [(Over.post (X := X) u).Faithful]
    [(Over.post (X := X) u).IsContinuous (J.over X) (K.over (u.obj X))]
    [(Over.post (X := X) u).IsCocontinuous (J.over X) (K.over (u.obj X))]
    [HasWeakSheafify (K.over (u.obj X)) (Type w)]
    [∀ P : (Over X)ᵒᵖ ⥤ Type w, (Over.post (X := X) u).op.HasLeftKanExtension P]
    [∀ P : (Over X)ᵒᵖ ⥤ Type w,
      (Over.post (X := X) u).op.HasPointwiseLeftKanExtension P]
    [PreservesFiniteLimits
      ((Over.post (X := X) u).sheafPullback (Type w) (J.over X) (K.over (u.obj X)))]
    [HasSheafify (J.over X) (Type w)]
    [∀ P : (Over X)ᵒᵖ ⥤ Type w,
      (Over.post (X := X) u).op.HasPointwiseRightKanExtension P] :
    (MorphismOfTopoiIn.comp
        ((Over.post (X := X) u).morphismOfTopoiInOfContinuous
          (J.over X) (K.over (u.obj X)))
        ((Over.post (X := X) u).morphismOfTopoiInOfCocontinuous
          (J.over X) (K.over (u.obj X)))).inverseImage ≅
      (MorphismOfTopoiIn.id (J.over X)).inverseImage :=
  compInverseImageIso (J.over X) (K.over (u.obj X)) (Over.post (X := X) u)

end Retraction

end CategoryTheory.Functor
