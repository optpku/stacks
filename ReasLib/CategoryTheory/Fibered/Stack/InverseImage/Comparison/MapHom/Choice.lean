/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
import ReasLib.CategoryTheory.Fibered.Stack.Hom.Precomposition.Lift.Coherence
public import ReasLib.CategoryTheory.Fibered.Stack.InverseImage.Comparison.MapHom.Choice.Pushforward
public import ReasLib.CategoryTheory.Fibered.Stack.InverseImage.Comparison.MapHom.HomComparison

/-!
# Choice coherence for the direct inverse-image morphism construction

This file records that changing the stackification quasi-inverse preserves the direct Hom
comparison and supplies the usual laws for its canonical choice isomorphism.
-/

@[expose] public section

universe uC uD vC vD w₀ w₁

namespace CategoryTheory

open Bicategory Limits
open scoped Bicategory

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

namespace StackOver.InverseImage.mapHom

variable {u : C ⥤ D}
variable [HasPullbacks C] [HasEqualizers C]
variable [PreservesLimitsOfShape WalkingCospan u]
variable [PreservesLimitsOfShape WalkingParallelPair u]
variable [u.IsContinuous J K]

variable {S S' : StackOver.{uC, vC,
  max w₀ (max uC (max uD (max vC vD))),
  max w₁ (max w₀ (max uC (max uD (max vC vD))))} J}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem inverseChoiceCounitApp
    {A B : Type*} [Category* A] [Category* B] {F : A ⥤ B}
    (e e' : Functor.QuasiInverse F) (X : B) :
    F.map ((e.inverseIso e').hom.app X) ≫ e'.counitIso.hom.app X =
      e.counitIso.hom.app X := by
  have h : (e.inverseIso e').hom.app X =
      (Equivalence.adjointifyη e'.unitIso e'.counitIso).hom.app (e.inverse.obj X) ≫
        e'.inverse.map (e.counitIso.hom.app X) := by
    dsimp [Functor.QuasiInverse.inverseIso, Iso.isoInverseOfIsoFunctor, Iso.isoCompInverse,
      Functor.QuasiInverse.adjointifyUnit, Equivalence.mk]
    simp only [Category.id_comp, Category.comp_id]
  rw [h, F.map_comp, Category.assoc]
  have hε := e'.counitIso.hom.naturality (e.counitIso.hom.app X)
  dsimp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at hε
  rw [hε, ← Category.assoc, Equivalence.adjointify_η_ε, Category.id_comp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem liftChoiceComparison
    {A B E : Type*} [Category* A] [Category* B] [Category* E] {F : A ⥤ B}
    (e e' : Functor.QuasiInverse F) (G : E ⥤ B) :
    Functor.isoWhiskerRight (Functor.QuasiInverse.liftFunctor.choiceIso e e' G) F ≪≫
        Functor.QuasiInverse.liftFunctor.comparisonIso e' G =
      Functor.QuasiInverse.liftFunctor.comparisonIso e G := by
  ext X
  dsimp [Functor.QuasiInverse.liftFunctor.choiceIso,
    Functor.QuasiInverse.liftFunctor.choiceNatIso,
    Functor.QuasiInverse.liftFunctor.comparisonIso,
    Functor.QuasiInverse.liftFunctor.comparisonNatIso, Functor.QuasiInverse.liftFunctor,
    Equivalence.congrRight, Functor.isoWhiskerRight, Functor.whiskeringRight,
    Functor.QuasiInverse.adjointifyUnit, Equivalence.mk]
  simpa only [Category.id_comp, Category.comp_id] using
    inverseChoiceCounitApp e e' (G.obj X)

private theorem liftChoiceRefl
    {A B E : Type*} [Category* A] [Category* B] [Category* E] {F : A ⥤ B}
    (e : Functor.QuasiInverse F) (G : E ⥤ B) :
    Functor.QuasiInverse.liftFunctor.choiceIso e e G =
      Iso.refl ((e.liftFunctor E).obj G) := by
  ext X
  apply e.adjointifyUnit.fullyFaithfulFunctor.map_injective
  apply (cancel_mono (e.counitIso.hom.app (G.obj X))).1
  change F.map ((e.inverseIso e).hom.app (G.obj X)) ≫ _ = F.map (𝟙 _) ≫ _
  rw [inverseChoiceCounitApp, F.map_id, Category.id_comp]

private theorem liftChoiceSymm
    {A B E : Type*} [Category* A] [Category* B] [Category* E] {F : A ⥤ B}
    (e e' : Functor.QuasiInverse F) (G : E ⥤ B) :
    (Functor.QuasiInverse.liftFunctor.choiceIso e e' G).symm =
      Functor.QuasiInverse.liftFunctor.choiceIso e' e G := by
  ext X
  apply e.adjointifyUnit.fullyFaithfulFunctor.map_injective
  apply (cancel_mono (e.counitIso.hom.app (G.obj X))).1
  change F.map ((e.inverseIso e').inv.app (G.obj X)) ≫ _ =
    F.map ((e'.inverseIso e).hom.app (G.obj X)) ≫ _
  rw [inverseChoiceCounitApp, ← inverseChoiceCounitApp e e' (G.obj X),
    ← Category.assoc, ← F.map_comp, Iso.inv_hom_id_app, F.map_id, Category.id_comp]

private theorem liftChoiceTrans
    {A B E : Type*} [Category* A] [Category* B] [Category* E] {F : A ⥤ B}
    (e e' e'' : Functor.QuasiInverse F) (G : E ⥤ B) :
    Functor.QuasiInverse.liftFunctor.choiceIso e e' G ≪≫
        Functor.QuasiInverse.liftFunctor.choiceIso e' e'' G =
      Functor.QuasiInverse.liftFunctor.choiceIso e e'' G := by
  ext X
  apply e.adjointifyUnit.fullyFaithfulFunctor.map_injective
  apply (cancel_mono (e''.counitIso.hom.app (G.obj X))).1
  change F.map ((e.inverseIso e').hom.app (G.obj X) ≫
      (e'.inverseIso e'').hom.app (G.obj X)) ≫ _ =
    F.map ((e.inverseIso e'').hom.app (G.obj X)) ≫ _
  rw [F.map_comp, Category.assoc, inverseChoiceCounitApp,
    inverseChoiceCounitApp, inverseChoiceCounitApp]

private theorem whiskerLeftComparison
    {A B E T : Type*} [Category* A] [Category* B] [Category* E] [Category* T]
    (L : E ⥤ A) {F G : A ⥤ B} {R : B ⥤ T} {M : A ⥤ T}
    (α : F ≅ G) (β : G ⋙ R ≅ M) (γ : F ⋙ R ≅ M)
    (h : Functor.isoWhiskerRight α R ≪≫ β = γ) :
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft L α) R ≪≫
        (Functor.associator L G R ≪≫ Functor.isoWhiskerLeft L β) =
      Functor.associator L F R ≪≫ Functor.isoWhiskerLeft L γ := by
  rw [Functor.isoWhiskerRight_left]
  simp only [Iso.trans_assoc, Iso.symm_self_id_assoc]
  rw [← Functor.isoWhiskerLeft_trans, h]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Changing the stackification quasi-inverse preserves the direct stackification comparison. -/
@[stacks 04WS "direct comparison choice coherence"]
theorem choiceIso.comparison
    (I : StackOver.InverseImage K u S)
    (I' : StackOver.InverseImage K u S')
    (h : FiberedCategoryOver.Pushforward.InversionChoice u
      S.toFiberedCategoryOver S'.toFiberedCategoryOver)
    (q q' : Functor.QuasiInverse
      (StackOver.Hom.precomp I'.target I.comparisonHom)) :
    Functor.isoWhiskerRight (choiceIso I I' h q q')
          (StackOver.Hom.precomp I'.target I.comparisonHom) ≪≫
        comparisonIso I I' h q' =
      comparisonIso I I' h q :=
  whiskerLeftComparison (StackOver.Pushforward.mapFunctor u h) _ _ _
    (liftChoiceComparison q q'
      (Bicategory.postcomp I.source I'.comparisonHom))

set_option maxHeartbeats 800000 in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The forward direct stackification-choice triangle commutes at every stack morphism. -/
@[stacks 04WS "direct comparison choice forward component"]
theorem choiceIso.hom.comparison_app
    (I : StackOver.InverseImage K u S)
    (I' : StackOver.InverseImage K u S')
    (h : FiberedCategoryOver.Pushforward.InversionChoice u
      S.toFiberedCategoryOver S'.toFiberedCategoryOver)
    (q q' : Functor.QuasiInverse
      (StackOver.Hom.precomp I'.target I.comparisonHom))
    (F : S ⟶ S') :
    (StackOver.Hom.precomp I'.target I.comparisonHom).map
          ((choiceIso I I' h q q').hom.app F) ≫
        (comparisonIso I I' h q').hom.app F =
      (comparisonIso I I' h q).hom.app F :=
  NatTrans.congr_app (congrArg Iso.hom (choiceIso.comparison I I' h q q')) F

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in
/-- The inverse direct stackification-choice triangle commutes at every stack morphism. -/
@[stacks 04WS "direct comparison choice inverse component"]
theorem choiceIso.inv.comparison_app
    (I : StackOver.InverseImage K u S)
    (I' : StackOver.InverseImage K u S')
    (h : FiberedCategoryOver.Pushforward.InversionChoice u
      S.toFiberedCategoryOver S'.toFiberedCategoryOver)
    (q q' : Functor.QuasiInverse
      (StackOver.Hom.precomp I'.target I.comparisonHom))
    (F : S ⟶ S') :
    (comparisonIso I I' h q').inv.app F ≫
        (StackOver.Hom.precomp I'.target I.comparisonHom).map
          ((choiceIso I I' h q q').inv.app F) =
      (comparisonIso I I' h q).inv.app F :=
  NatTrans.congr_app (congrArg Iso.inv (choiceIso.comparison I I' h q q')) F

set_option maxHeartbeats 800000 in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Changing the stackification quasi-inverse preserves the direct comparison after applying the
canonical Hom functor. -/
@[stacks 04WS "direct Hom-functor choice coherence"]
theorem choiceIso.homFunctorComparison
    (I : StackOver.InverseImage K u S)
    (I' : StackOver.InverseImage K u S')
    (h : FiberedCategoryOver.Pushforward.InversionChoice u
      S.toFiberedCategoryOver S'.toFiberedCategoryOver)
    (q q' : Functor.QuasiInverse
      (StackOver.Hom.precomp I'.target I.comparisonHom)) :
    Functor.isoWhiskerRight (choiceIso I I' h q q') (homFunctor I I'.target) ≪≫
        homFunctorIso I I' h q' =
      homFunctorIso I I' h q := by
  apply Iso.ext
  apply NatTrans.ext
  funext F
  simp only [Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Iso.trans_hom, NatTrans.comp_app, homFunctorIso, NatIso.ofComponents_hom_app,
    homComparisonApp, Iso.app_hom, Functor.mapIso_hom, homFunctor, Functor.comp_map]
  rw [← Category.assoc, ← Functor.map_comp, ← Functor.map_comp]
  erw [choiceIso.hom.comparison_app I I' h q q' F]

set_option maxHeartbeats 800000 in
/-- The forward direct-choice comparison triangle commutes at every stack morphism. -/
@[stacks 04WS "direct Hom-functor choice forward component"]
theorem choiceIso.hom.homFunctorComparison_app
    (I : StackOver.InverseImage K u S)
    (I' : StackOver.InverseImage K u S')
    (h : FiberedCategoryOver.Pushforward.InversionChoice u
      S.toFiberedCategoryOver S'.toFiberedCategoryOver)
    (q q' : Functor.QuasiInverse
      (StackOver.Hom.precomp I'.target I.comparisonHom))
    (F : S ⟶ S') :
    (homFunctor I I'.target).map ((choiceIso I I' h q q').hom.app F) ≫
        (homFunctorIso I I' h q').hom.app F =
      (homFunctorIso I I' h q).hom.app F :=
  NatTrans.congr_app (congrArg Iso.hom (choiceIso.homFunctorComparison I I' h q q')) F

set_option maxHeartbeats 800000 in
/-- The inverse direct-choice comparison triangle commutes at every stack morphism. -/
@[stacks 04WS "direct Hom-functor choice inverse component"]
theorem choiceIso.inv.homFunctorComparison_app
    (I : StackOver.InverseImage K u S)
    (I' : StackOver.InverseImage K u S')
    (h : FiberedCategoryOver.Pushforward.InversionChoice u
      S.toFiberedCategoryOver S'.toFiberedCategoryOver)
    (q q' : Functor.QuasiInverse
      (StackOver.Hom.precomp I'.target I.comparisonHom))
    (F : S ⟶ S') :
    (homFunctorIso I I' h q').inv.app F ≫
        (homFunctor I I'.target).map ((choiceIso I I' h q q').inv.app F) =
      (homFunctorIso I I' h q).inv.app F :=
  NatTrans.congr_app (congrArg Iso.inv (choiceIso.homFunctorComparison I I' h q q')) F

/-- The direct choice comparison from a stackification lift to itself is the identity. -/
@[simp, stacks 04WS "direct comparison choice reflexivity"]
theorem choiceIso.refl
    (I : StackOver.InverseImage K u S)
    (I' : StackOver.InverseImage K u S')
    (h : FiberedCategoryOver.Pushforward.InversionChoice u
      S.toFiberedCategoryOver S'.toFiberedCategoryOver)
    (q : Functor.QuasiInverse
      (StackOver.Hom.precomp I'.target I.comparisonHom)) :
    choiceIso I I' h q q = Iso.refl (mapHom I I' h q) := by
  change Functor.isoWhiskerLeft (StackOver.Pushforward.mapFunctor u h)
      (Functor.QuasiInverse.liftFunctor.choiceIso q q
        (Bicategory.postcomp I.source I'.comparisonHom)) = _
  rw [liftChoiceRefl]
  rfl

/-- Reversing a direct choice comparison exchanges its stackification lifts. -/
@[simp, stacks 04WS "direct comparison choice symmetry"]
theorem choiceIso.symm
    (I : StackOver.InverseImage K u S)
    (I' : StackOver.InverseImage K u S')
    (h : FiberedCategoryOver.Pushforward.InversionChoice u
      S.toFiberedCategoryOver S'.toFiberedCategoryOver)
    (q q' : Functor.QuasiInverse
      (StackOver.Hom.precomp I'.target I.comparisonHom)) :
    (choiceIso I I' h q q').symm = choiceIso I I' h q' q := by
  change (Functor.isoWhiskerLeft (StackOver.Pushforward.mapFunctor u h)
      (Functor.QuasiInverse.liftFunctor.choiceIso q q'
        (Bicategory.postcomp I.source I'.comparisonHom))).symm = _
  rw [Functor.isoWhiskerLeft_symm, liftChoiceSymm]
  rfl

/-- Direct choice comparisons compose transitively. -/
@[stacks 04WS "direct comparison choice transitivity"]
theorem choiceIso.trans
    (I : StackOver.InverseImage K u S)
    (I' : StackOver.InverseImage K u S')
    (h : FiberedCategoryOver.Pushforward.InversionChoice u
      S.toFiberedCategoryOver S'.toFiberedCategoryOver)
    (q q' q'' : Functor.QuasiInverse
      (StackOver.Hom.precomp I'.target I.comparisonHom)) :
    choiceIso I I' h q q' ≪≫ choiceIso I I' h q' q'' =
      choiceIso I I' h q q'' := by
  change Functor.isoWhiskerLeft (StackOver.Pushforward.mapFunctor u h)
      (Functor.QuasiInverse.liftFunctor.choiceIso q q'
        (Bicategory.postcomp I.source I'.comparisonHom)) ≪≫
      Functor.isoWhiskerLeft (StackOver.Pushforward.mapFunctor u h)
        (Functor.QuasiInverse.liftFunctor.choiceIso q' q''
          (Bicategory.postcomp I.source I'.comparisonHom)) = _
  rw [← Functor.isoWhiskerLeft_trans, liftChoiceTrans]
  rfl

end StackOver.InverseImage.mapHom

end CategoryTheory
