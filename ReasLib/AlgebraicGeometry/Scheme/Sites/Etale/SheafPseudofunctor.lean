/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Small
public import Mathlib.CategoryTheory.Sites.Descent.DescentData
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.EtaleSheaf

/-- Pullback of Type-valued sheaves along a morphism of small étale sites. -/
noncomputable abbrev pullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Sheaf Y.smallEtaleTopology (Type (u + 1)) ⥤
      Sheaf X.smallEtaleTopology (Type (u + 1)) :=
  (smallEtalePullback f).sheafPullback (Type (u + 1))
    Y.smallEtaleTopology X.smallEtaleTopology

/-- Pullback of small étale sheaves along an identity is canonically the identity functor. -/
noncomputable def pullbackId (X : Scheme.{u}) :
    pullback (𝟙 X) ≅ 𝟭 (Sheaf X.smallEtaleTopology (Type (u + 1))) :=
  let siteIso : smallEtalePullback (𝟙 X) ≅ 𝟭 X.Etale :=
    conjugateIsoEquiv
      (MorphismProperty.Over.mapPullbackAdj @Etale ⊤ (𝟙 X)
        (inferInstance : Etale (𝟙 X)) trivial)
      Adjunction.id
      (MorphismProperty.Over.mapId (P := @Etale) (Q := ⊤) X).symm
  let e := Adjunction.leftAdjointIdIso
    ((smallEtalePullback (𝟙 X)).sheafAdjunctionContinuous (Type (u + 1))
      X.smallEtaleTopology X.smallEtaleTopology)
    (Functor.sheafPushforwardContinuousId' siteIso
      (Type (u + 1)) X.smallEtaleTopology)
  NatIso.ofComponents (fun F ↦ e.app F) (fun φ ↦ e.hom.naturality φ)

/-- Successive pullbacks of small étale sheaves are canonically pullback along the composite. -/
noncomputable def pullbackComp {X Y Z : Scheme.{u}} (f : Y ⟶ Z) (g : X ⟶ Y) :
    pullback f ⋙ pullback g ≅ pullback (g ≫ f) :=
  let siteIso : smallEtalePullback f ⋙ smallEtalePullback g ≅
      smallEtalePullback (g ≫ f) :=
    (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) g f).symm
  let e := Adjunction.leftAdjointCompIso
    ((smallEtalePullback f).sheafAdjunctionContinuous (Type (u + 1))
      Z.smallEtaleTopology Y.smallEtaleTopology)
    ((smallEtalePullback g).sheafAdjunctionContinuous (Type (u + 1))
      Y.smallEtaleTopology X.smallEtaleTopology)
    ((smallEtalePullback (g ≫ f)).sheafAdjunctionContinuous (Type (u + 1))
      Z.smallEtaleTopology X.smallEtaleTopology)
    (Functor.sheafPushforwardContinuousComp' siteIso
      (Type (u + 1)) Z.smallEtaleTopology Y.smallEtaleTopology
        X.smallEtaleTopology)
  NatIso.ofComponents (fun F ↦ e.app F) (fun φ ↦ e.hom.naturality φ)

section

open CategoryTheory.Functor

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private lemma pullbackComp_transport {X Y Z : Scheme.{u}} (f : Y ⟶ Z) (g : X ⟶ Y)
    (gf : X ⟶ Z) (h : gf = g ≫ f) :
    pullbackComp f g ≪≫ eqToIso (congrArg pullback h.symm) =
      Adjunction.leftAdjointCompIso
        ((smallEtalePullback f).sheafAdjunctionContinuous (Type (u + 1))
          Z.smallEtaleTopology Y.smallEtaleTopology)
        ((smallEtalePullback g).sheafAdjunctionContinuous (Type (u + 1))
          Y.smallEtaleTopology X.smallEtaleTopology)
        ((smallEtalePullback gf).sheafAdjunctionContinuous (Type (u + 1))
          Z.smallEtaleTopology X.smallEtaleTopology)
        (Functor.sheafPushforwardContinuousComp'
          (F := smallEtalePullback f) (G := smallEtalePullback g)
          (FG := smallEtalePullback gf)
          (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) g f gf h).symm
          (Type (u + 1)) Z.smallEtaleTopology Y.smallEtaleTopology X.smallEtaleTopology) := by
  subst gf
  rfl

private lemma pullbackComp_right_unitor {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pullbackComp f (𝟙 X) ≪≫ eqToIso (congrArg pullback (Category.id_comp f)) =
      isoWhiskerLeft (pullback f) (pullbackId X) ≪≫ Functor.rightUnitor _ := by
  let siteId : smallEtalePullback (𝟙 X) ≅ 𝟭 X.Etale :=
    conjugateIsoEquiv
      (MorphismProperty.Over.mapPullbackAdj @Etale ⊤ (𝟙 X)
        (inferInstance : Etale (𝟙 X)) trivial)
      Adjunction.id
      (MorphismProperty.Over.mapId (P := @Etale) (Q := ⊤) X).symm
  let eId := Functor.sheafPushforwardContinuousId' siteId
    (Type (u + 1)) X.smallEtaleTopology
  let eComp := Functor.sheafPushforwardContinuousComp'
    (F := smallEtalePullback f) (G := smallEtalePullback (𝟙 X))
    (FG := smallEtalePullback f)
    (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) (𝟙 X) f f
      (Category.id_comp f).symm).symm
    (Type (u + 1)) Y.smallEtaleTopology X.smallEtaleTopology X.smallEtaleTopology
  have hh : eComp = isoWhiskerRight eId
      ((smallEtalePullback f).sheafPushforwardContinuous
        (Type (u + 1)) Y.smallEtaleTopology X.smallEtaleTopology) ≪≫
        Functor.leftUnitor _ := by
    ext M U : 6
    dsimp [eComp, eId, Functor.sheafPushforwardContinuousComp',
      Functor.sheafPushforwardContinuousId', Functor.sheafPushforwardContinuousComp,
      Functor.sheafPushforwardContinuousId, Functor.sheafPushforwardContinuousIso,
      Functor.sheafPushforwardContinuousNatTrans]
    simp only [Category.id_comp, Category.comp_id]
    apply congrArg (fun k : (smallEtalePullback f).obj (Opposite.unop U) ⟶
      (smallEtalePullback (𝟙 X)).obj ((smallEtalePullback f).obj (Opposite.unop U)) ↦
      M.obj.map k.op)
    apply MorphismProperty.Over.Hom.ext
    apply Limits.pullback.hom_ext
    · apply Limits.pullback.hom_ext <;>
        simp [siteId, conjugateIsoEquiv, conjugateEquiv_apply_app,
          MorphismProperty.Over.pullbackComp, MorphismProperty.Over.pullback,
          MorphismProperty.Over.mapPullbackAdj]
    · simp [siteId, conjugateIsoEquiv, conjugateEquiv_apply_app,
        MorphismProperty.Over.pullbackComp, MorphismProperty.Over.pullback,
        MorphismProperty.Over.mapPullbackAdj]
  rw [pullbackComp_transport f (𝟙 X) f (Category.id_comp f).symm]
  exact Adjunction.leftAdjointCompIso_comp_id _ _ eComp eId hh

private lemma pullbackComp_left_unitor {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pullbackComp (𝟙 Y) f ≪≫ eqToIso (congrArg pullback (Category.comp_id f)) =
      isoWhiskerRight (pullbackId Y) (pullback f) ≪≫ Functor.leftUnitor _ := by
  let siteId : smallEtalePullback (𝟙 Y) ≅ 𝟭 Y.Etale :=
    conjugateIsoEquiv
      (MorphismProperty.Over.mapPullbackAdj @Etale ⊤ (𝟙 Y)
        (inferInstance : Etale (𝟙 Y)) trivial)
      Adjunction.id
      (MorphismProperty.Over.mapId (P := @Etale) (Q := ⊤) Y).symm
  let eId := Functor.sheafPushforwardContinuousId' siteId
    (Type (u + 1)) Y.smallEtaleTopology
  let eComp := Functor.sheafPushforwardContinuousComp'
    (F := smallEtalePullback (𝟙 Y)) (G := smallEtalePullback f)
    (FG := smallEtalePullback f)
    (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) f (𝟙 Y) f
      (Category.comp_id f).symm).symm
    (Type (u + 1)) Y.smallEtaleTopology Y.smallEtaleTopology X.smallEtaleTopology
  have hh : eComp = isoWhiskerLeft
      ((smallEtalePullback f).sheafPushforwardContinuous
        (Type (u + 1)) Y.smallEtaleTopology X.smallEtaleTopology) eId ≪≫
        Functor.rightUnitor _ := by
    ext M U : 6
    dsimp [eComp, eId, Functor.sheafPushforwardContinuousComp',
      Functor.sheafPushforwardContinuousId', Functor.sheafPushforwardContinuousComp,
      Functor.sheafPushforwardContinuousId, Functor.sheafPushforwardContinuousIso,
      Functor.sheafPushforwardContinuousNatTrans]
    simp only [Category.id_comp, Category.comp_id]
    apply congrArg (fun k : (smallEtalePullback f).obj (Opposite.unop U) ⟶
      (smallEtalePullback f).obj ((smallEtalePullback (𝟙 Y)).obj (Opposite.unop U)) ↦
      M.obj.map k.op)
    apply MorphismProperty.Over.Hom.ext
    have comp_left {A B C : X.Etale} (a : A ⟶ B) (b : B ⟶ C) :
        (a ≫ b).left = a.left ≫ b.left := rfl
    apply Limits.pullback.hom_ext
    · apply Limits.pullback.hom_ext <;>
        simp [siteId, conjugateIsoEquiv, conjugateEquiv_apply_app,
          MorphismProperty.Over.pullbackComp, MorphismProperty.Over.pullback,
          MorphismProperty.Over.mapPullbackAdj, comp_left, Limits.pullback.condition]
    · simp [siteId, conjugateIsoEquiv, conjugateEquiv_apply_app,
        MorphismProperty.Over.pullbackComp, MorphismProperty.Over.pullback,
        MorphismProperty.Over.mapPullbackAdj, comp_left]
  rw [pullbackComp_transport (𝟙 Y) f f (Category.comp_id f).symm]
  exact Adjunction.leftAdjointCompIso_id_comp _ _ eComp eId hh

private lemma pullbackComp_associator {W X Y Z : Scheme.{u}}
    (f : Y ⟶ Z) (g : X ⟶ Y) (h : W ⟶ X) :
    isoWhiskerLeft (pullback f) (pullbackComp g h) ≪≫ pullbackComp f (h ≫ g) ≪≫
      eqToIso (congrArg pullback (Category.assoc h g f)) =
    (Functor.associator (pullback f) (pullback g) (pullback h)).symm ≪≫
      isoWhiskerRight (pullbackComp f g) (pullback h) ≪≫ pullbackComp (g ≫ f) h := by
  rw [pullbackComp_transport f (h ≫ g) (h ≫ g ≫ f) (Category.assoc h g f).symm]
  apply Adjunction.leftAdjointCompIso_assoc
  ext M U : 6
  dsimp [Functor.sheafPushforwardContinuousComp',
    Functor.sheafPushforwardContinuousComp, Functor.sheafPushforwardContinuousIso,
    Functor.sheafPushforwardContinuousNatTrans]
  simp only [Category.id_comp, ← Functor.map_comp, ← op_comp]
  apply congrArg (fun k : (smallEtalePullback (h ≫ g ≫ f)).obj (Opposite.unop U) ⟶
    (smallEtalePullback h).obj ((smallEtalePullback g).obj
      ((smallEtalePullback f).obj (Opposite.unop U))) ↦ M.obj.map k.op)
  apply MorphismProperty.Over.Hom.ext
  have comp_left {A B C : W.Etale} (a : A ⟶ B) (b : B ⟶ C) :
      (a ≫ b).left = a.left ≫ b.left := rfl
  apply Limits.pullback.hom_ext
  · apply Limits.pullback.hom_ext
    · apply Limits.pullback.hom_ext <;>
        simp [MorphismProperty.Over.pullbackComp, MorphismProperty.Over.pullback,
          comp_left, Category.assoc]
    · simp [MorphismProperty.Over.pullbackComp, MorphismProperty.Over.pullback,
        comp_left, Category.assoc]
  · simp [MorphismProperty.Over.pullbackComp, MorphismProperty.Over.pullback,
      comp_left, Category.assoc]

/-- The contravariant pseudofunctor of Type-valued sheaves on small étale sites. -/
noncomputable def pseudofunctor :
    Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat :=
  LocallyDiscrete.mkPseudofunctor
    (fun X ↦ Cat.of (Sheaf X.unop.smallEtaleTopology (Type (u + 1))))
    (fun f ↦ (pullback f.unop).toCatHom)
    (fun X ↦ Cat.Hom.isoMk (pullbackId X.unop))
    (fun f g ↦ Cat.Hom.isoMk (pullbackComp f.unop g.unop).symm)
    (fun f g h ↦ by
      apply Cat.Hom₂.ext
      change (pullbackComp (g.unop ≫ f.unop) h.unop).inv ≫
          (isoWhiskerRight (pullbackComp f.unop g.unop) (pullback h.unop)).inv ≫
          (Functor.associator _ _ _).hom ≫
          (isoWhiskerLeft (pullback f.unop) (pullbackComp g.unop h.unop)).hom ≫
          (pullbackComp f.unop (h.unop ≫ g.unop)).hom =
        eqToHom (congrArg pullback (Category.assoc h.unop g.unop f.unop).symm)
      have hc := congrArg Iso.hom (pullbackComp_associator f.unop g.unop h.unop)
      dsimp only [Iso.trans_hom, eqToIso] at hc
      apply (cancel_mono
        (eqToHom (congrArg pullback (Category.assoc h.unop g.unop f.unop)))).1
      simp only [Category.assoc] at hc ⊢
      rw [hc]
      simp only [Iso.symm_hom, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id]
      simp)
    (fun f ↦ by
      apply Cat.Hom₂.ext
      change (pullbackComp (𝟙 _) f.unop).inv ≫
          (isoWhiskerRight (pullbackId _) (pullback f.unop)).hom ≫
          (Functor.leftUnitor _).hom = eqToHom (congrArg pullback (Category.comp_id f.unop))
      have h := congrArg Iso.hom (pullbackComp_left_unitor f.unop)
      dsimp only [Iso.trans_hom] at h
      rw [← h]
      simp)
    (fun f ↦ by
      apply Cat.Hom₂.ext
      change (pullbackComp f.unop (𝟙 _)).inv ≫
          (isoWhiskerLeft (pullback f.unop) (pullbackId _)).hom ≫
          (Functor.rightUnitor _).hom = eqToHom (congrArg pullback (Category.id_comp f.unop))
      have h := congrArg Iso.hom (pullbackComp_right_unitor f.unop)
      dsimp only [Iso.trans_hom] at h
      rw [← h]
      simp)

end

/-- The fiber of `pseudofunctor` at `X` is the category of Type-valued small étale sheaves. -/
theorem pseudofunctor_obj (X : Scheme.{u}) :
    pseudofunctor.obj (.mk (.op X)) =
      Cat.of (Sheaf X.smallEtaleTopology (Type (u + 1))) := rfl

/-- The action of `pseudofunctor` on a scheme morphism is small étale sheaf pullback. -/
theorem pseudofunctor_map {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (pseudofunctor.map f.op.toLoc).toFunctor = pullback f := rfl

open CategoryTheory.Pseudofunctor in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A section of a scheme morphism makes the canonical singleton descent-data functor an equivalence. -/
theorem descentIsEquivalenceOfSection {X Y : Scheme.{u}} (f : X ⟶ Y)
    (split : SplitEpi f) :
    (pseudofunctor.toDescentData (fun _ : PUnit.{1} ↦ f)).IsEquivalence := by
  have hId : (pseudofunctor.toDescentData (fun _ : PUnit.{1} ↦ 𝟙 Y)).IsEquivalence := by
    let ev : pseudofunctor.DescentData (fun _ : PUnit.{1} ↦ 𝟙 Y) ⥤
        pseudofunctor.obj (.mk (Opposite.op Y)) :=
      { obj D := D.obj PUnit.unit
        map φ := φ.hom PUnit.unit }
    let e := Cat.Hom.toNatIso (pseudofunctor.mapId (.mk (Opposite.op Y)))
    refine Functor.IsEquivalence.mk' ev e.symm ?_
    refine NatIso.ofComponents (fun D ↦ DescentData.isoMk (fun _ ↦ e.app (D.obj PUnit.unit)) ?_) ?_
    · intro T q i j a b ha hb
      have hab : a = b := by simpa using ha.trans hb.symm
      subst b
      cases i
      cases j
      change (pseudofunctor.map a.op.toLoc).toFunctor.map (e.app (D.obj PUnit.unit)).hom ≫
          D.hom q a a ha ha =
        (DescentData.ofObj (F := pseudofunctor) (f := fun _ : PUnit.{1} ↦ 𝟙 Y)
          (D.obj PUnit.unit)).hom q a a ha ha ≫
          (pseudofunctor.map a.op.toLoc).toFunctor.map (e.app (D.obj PUnit.unit)).hom
      have hE := (DescentData.ofObj (F := pseudofunctor)
        (f := fun _ : PUnit.{1} ↦ 𝟙 Y) (D.obj PUnit.unit)).hom_self q (i := PUnit.unit) a ha
      rw [D.hom_self q a ha, hE]
      exact (Category.comp_id _).trans (Category.id_comp _).symm
    · intro D E φ
      ext i
      cases i
      exact e.hom.naturality (φ.hom PUnit.unit)
  let w : ∀ _ : PUnit.{1}, split.section_ ≫ f = 𝟙 Y ≫ 𝟙 Y :=
    fun _ ↦ by simpa using split.id
  let e := DescentData.pullFunctorEquivalence pseudofunctor
    (f := fun _ : PUnit.{1} ↦ f) (f' := fun _ : PUnit.{1} ↦ 𝟙 Y)
    (Iso.refl Y) (α := fun _ ↦ PUnit.unit) (p' := fun _ ↦ split.section_) w
    (β := fun _ ↦ PUnit.unit) (q' := fun _ ↦ f) (by simp)
  let iso : pseudofunctor.toDescentData (fun _ : PUnit.{1} ↦ f) ⋙ e.functor ≅
      pseudofunctor.toDescentData (fun _ : PUnit.{1} ↦ 𝟙 Y) :=
    DescentData.toDescentDataCompPullFunctorIso pseudofunctor
      (f := fun _ : PUnit.{1} ↦ f) (f' := fun _ : PUnit.{1} ↦ 𝟙 Y)
      (p := 𝟙 Y) (α := fun _ ↦ PUnit.unit) (p' := fun _ ↦ split.section_) w ≪≫
      Functor.isoWhiskerRight (Cat.Hom.toNatIso (pseudofunctor.mapId (.mk (Opposite.op Y)))) _ ≪≫
        Functor.leftUnitor _
  haveI := hId
  haveI : (pseudofunctor.toDescentData (fun _ : PUnit.{1} ↦ f) ⋙ e.functor).IsEquivalence :=
    Functor.isEquivalence_of_iso iso.symm
  exact Functor.isEquivalence_of_comp_right _ e.functor

end AlgebraicGeometry.Scheme.EtaleSheaf
