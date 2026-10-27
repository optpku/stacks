/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Ringed.Map
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Localization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.Spaces
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.PresentationRestriction

/-!
# Étale localization of spaces-étale ringed sites

An étale morphism of algebraic spaces identifies the spaces-étale ringed site of its domain
with the slice ringed site of its codomain, including the restricted structure sheaf.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Structured-arrow triangle in `Y_spaces,étale`: composing the chart morphism with the
structure morphism of `Z` recovers the structure morphism of the small étale chart. -/
private theorem spacesEtaleLocalization_structuredArrow_w {Z : spacesEtaleSite Y}
    (a : StructuredArrow (op Z) (smallEtaleToSpaces Y).op) :
    a.hom.unop.left ≫ Z.hom = a.right.unop.hom :=
  MorphismProperty.Over.w a.hom.unop

/-- Postcomposition of a chart over a slice object commutes with its map to the base. -/
private theorem spacesEtaleLocalizationDiagramObj_w (f : X ⟶ Y) [Etale f]
    (W : Over (spacesEtaleSite.mk f))
    (a : StructuredArrow (op (spacesEtaleLocalizationInverseObj f W))
      (smallEtaleToSpaces X).op) :
    a.hom.unop.left ≫ W.left.hom = a.right.unop.hom ≫ f := by
  have h : a.hom.unop.left ≫ W.hom.left = a.right.unop.hom :=
    spacesEtaleLocalization_structuredArrow_w a
  exact (congrArg (fun k : W.left.left ⟶ Y ↦ a.hom.unop.left ≫ k)
    (MorphismProperty.Over.w W.hom).symm).trans
      ((Category.assoc a.hom.unop.left W.hom.left f).symm.trans
        (congrArg (fun k : _ ⟶ X ↦ k ≫ f) h))

/-- The image of a structured arrow over `InverseObj W` under postcomposition along `f`. -/
private def spacesEtaleLocalizationDiagramObj (f : X ⟶ Y) [Etale f]
    (W : Over (spacesEtaleSite.mk f))
    (a : StructuredArrow (op (spacesEtaleLocalizationInverseObj f W))
      (smallEtaleToSpaces X).op) :
    StructuredArrow (op W.left) (smallEtaleToSpaces Y).op :=
  StructuredArrow.mk
    ((MorphismProperty.Over.homMk a.hom.unop.left (spacesEtaleLocalizationDiagramObj_w f W a) :
        (smallEtaleToSpaces Y).obj
          ((Modules.restrictPostcompose f).obj a.right.unop) ⟶ W.left).op)

/-- Evaluation on scheme charts respects a change of chart over the same space. -/
private theorem spacesEtaleLocalizationEvaluation_naturality (X : AlgebraicSpace S)
    (Q : Sheaf (smallEtaleTopology X) RingCat.{u}) {W : spacesEtaleSite X}
    {U V : smallEtaleSite X} (a : (smallEtaleToSpaces X).obj U ⟶ W)
    (b : (smallEtaleToSpaces X).obj V ⟶ W) (g : V ⟶ U)
    (h : (smallEtaleToSpaces X).map g ≫ a = b) :
    EtaleRingedTopos.ringExtensionEvaluation X Q b =
      EtaleRingedTopos.ringExtensionEvaluation X Q a ≫ Q.obj.map g.op := by
  let R := ((EtaleRingedTopos.ringExtension X).obj Q).obj
  let t := ((EtaleRingedTopos.ringExtensionRestrictionIso X).hom.app Q).hom
  change R.map b.op ≫ t.app (op V) =
    (R.map a.op ≫ t.app (op U)) ≫ Q.obj.map g.op
  calc
    R.map b.op ≫ t.app (op V) =
        R.map a.op ≫ (R.map ((smallEtaleToSpaces X).map g).op ≫ t.app (op V)) := by
      rw [← h, op_comp, R.map_comp, Category.assoc]
    _ = R.map a.op ≫ (t.app (op U) ≫ Q.obj.map g.op) :=
      congrArg (fun k ↦ R.map a.op ≫ k) (t.naturality g.op)
    _ = (R.map a.op ≫ t.app (op U)) ≫ Q.obj.map g.op :=
      (Category.assoc _ _ _).symm

/-- Evaluation on a fixed scheme chart respects a change of its target. -/
private theorem spacesEtaleLocalizationEvaluation_precomp (X : AlgebraicSpace S)
    (Q : Sheaf (smallEtaleTopology X) RingCat.{u}) {W W' : spacesEtaleSite X}
    (g : W' ⟶ W) {U : smallEtaleSite X} (a : (smallEtaleToSpaces X).obj U ⟶ W') :
    ((EtaleRingedTopos.ringExtension X).obj Q).obj.map g.op ≫
        EtaleRingedTopos.ringExtensionEvaluation X Q a =
      EtaleRingedTopos.ringExtensionEvaluation X Q (a ≫ g) := by
  let R := ((EtaleRingedTopos.ringExtension X).obj Q).obj
  let t := ((EtaleRingedTopos.ringExtensionRestrictionIso X).hom.app Q).hom.app (op U)
  change R.map g.op ≫ (R.map a.op ≫ t) = R.map (g.op ≫ a.op) ≫ t
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun k ↦ k ≫ t) (R.map_comp g.op a.op).symm)

set_option backward.isDefEq.respectTransparency false in
/-- The specified small-limit lift recovers each of its small-chart cone maps. -/
private theorem spacesEtaleLocalizationLift_fac (X : AlgebraicSpace S)
    (Q : Sheaf (smallEtaleTopology X) RingCat.{u}) (W : spacesEtaleSite X)
    (c : Cone (StructuredArrow.proj (op W) (smallEtaleToSpaces X).op ⋙ Q.obj))
    (a : StructuredArrow (op W) (SpacesEtale.AtlasCharts.inclusion X).op) :
    EtaleRingedTopos.ringExtensionLift X Q W c ≫
        (((EtaleRingedTopos.ringExtension X).obj Q).obj.map a.hom ≫
          (((SpacesEtale.AtlasCharts.inclusion X).op.ranCounit.app
            ((EtaleRingedTopos.ringSmallEquivalence X).functor.obj Q).obj).app a.right)) =
      c.π.app
        (StructuredArrow.mk
          (Y := op ((SmallEtale.AtlasCharts.inclusion X).obj a.right.unop)) a.hom) := by
  letI := EtaleRingedTopos.ringChartLimits X
  let l := limit.lift _ (EtaleRingedTopos.ringExtensionSmallCone X Q W c)
  have hf := Functor.ranObjObjIsoLimit_inv_π (SpacesEtale.AtlasCharts.inclusion X).op
    ((EtaleRingedTopos.ringSmallEquivalence X).functor.obj Q).obj (op W) a
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k ↦ l ≫ k) hf).trans (limit.lift_π _ a))

set_option backward.isDefEq.respectTransparency false in
/-- A compatible family of cone maps gives a natural map into the specified ring extension. -/
private theorem spacesEtaleLocalizationLift_naturality (X : AlgebraicSpace S)
    (Q : Sheaf (smallEtaleTopology X) RingCat.{u})
    {W W' : spacesEtaleSite X} (g : W' ⟶ W)
    (c : Cone (StructuredArrow.proj (op W) (smallEtaleToSpaces X).op ⋙ Q.obj))
    (c' : Cone (StructuredArrow.proj (op W') (smallEtaleToSpaces X).op ⋙ Q.obj))
    (q : c.pt ⟶ c'.pt)
    (h : ∀ a : StructuredArrow (op W') (smallEtaleToSpaces X).op,
      q ≫ c'.π.app a = c.π.app (StructuredArrow.mk (g.op ≫ a.hom))) :
    q ≫ EtaleRingedTopos.ringExtensionLift X Q W' c' =
      EtaleRingedTopos.ringExtensionLift X Q W c ≫
        ((EtaleRingedTopos.ringExtension X).obj Q).obj.map g.op := by
  letI := EtaleRingedTopos.ringChartLimits X
  apply (cancel_mono
    ((SpacesEtale.AtlasCharts.inclusion X).op.ranObjObjIsoLimit
      ((EtaleRingedTopos.ringSmallEquivalence X).functor.obj Q).obj (op W')).hom).mp
  apply limit.hom_ext
  intro a
  simp only [Category.assoc, Functor.ranObjObjIsoLimit_hom_π]
  have hh :=
    (congrArg (fun k ↦ q ≫ k) (spacesEtaleLocalizationLift_fac X Q W' c' a)).trans
      ((h (StructuredArrow.mk
        (Y := op ((SmallEtale.AtlasCharts.inclusion X).obj a.right.unop)) a.hom)).trans
          (spacesEtaleLocalizationLift_fac X Q W c
            (StructuredArrow.mk (g.op ≫ a.hom))).symm)
  let R := ((EtaleRingedTopos.ringExtension X).obj Q).obj
  let t := ((SpacesEtale.AtlasCharts.inclusion X).op.ranCounit.app
    ((EtaleRingedTopos.ringSmallEquivalence X).functor.obj Q).obj).app a.right
  change q ≫ EtaleRingedTopos.ringExtensionLift X Q W' c' ≫ (R.map a.hom ≫ t) =
    EtaleRingedTopos.ringExtensionLift X Q W c ≫ (R.map (g.op ≫ a.hom) ≫ t) at hh
  have hm : R.map (g.op ≫ a.hom) ≫ t = R.map g.op ≫ (R.map a.hom ≫ t) :=
    (congrArg (fun k ↦ k ≫ t) (R.map_comp g.op a.hom)).trans (Category.assoc _ _ _)
  exact hh.trans (congrArg (fun k ↦ EtaleRingedTopos.ringExtensionLift X Q W c ≫ k) hm)

/-- The forward chart evaluations form a cone. -/
private theorem spacesEtaleLocalizationHomCone_naturality (f : X ⟶ Y) [Etale f]
    (W : Over (spacesEtaleSite.mk f))
    {a b : StructuredArrow (op (spacesEtaleLocalizationInverseObj f W))
      (smallEtaleToSpaces X).op} (g : a ⟶ b) :
    𝟙 ((spacesStructureSheaf Y).obj.obj (op W.left)) ≫
        (EtaleRingedTopos.ringExtensionEvaluation Y (structureSheaf Y)
            (spacesEtaleLocalizationDiagramObj f W b).hom.unop ≫
          (Modules.restrictStructureMapInv f).hom.app b.right) =
      (EtaleRingedTopos.ringExtensionEvaluation Y (structureSheaf Y)
          (spacesEtaleLocalizationDiagramObj f W a).hom.unop ≫
        (Modules.restrictStructureMapInv f).hom.app a.right) ≫
        (structureSheaf X).obj.map g.right := by
  change 𝟙 _ ≫
      (EtaleRingedTopos.ringExtensionEvaluation Y (structureSheaf Y)
          (spacesEtaleLocalizationDiagramObj f W b).hom.unop ≫ 𝟙 _) =
    (EtaleRingedTopos.ringExtensionEvaluation Y (structureSheaf Y)
        (spacesEtaleLocalizationDiagramObj f W a).hom.unop ≫ 𝟙 _) ≫
      (structureSheaf X).obj.map g.right
  simp only [Category.id_comp, Category.comp_id]
  apply spacesEtaleLocalizationEvaluation_naturality Y (structureSheaf Y)
    _ _ ((Modules.restrictPostcompose f).map g.right.unop)
  apply MorphismProperty.Over.Hom.ext
  exact congrArg (fun k ↦ k.unop.left) (StructuredArrow.w g)

/-- The forward structure-sheaf component is the lift of the chart evaluations followed by
identity-on-sections étale restriction. -/
def spacesEtaleLocalizationIsoHomStructureSheaf_app (f : X ⟶ Y) [Etale f]
    (W : (Over (spacesEtaleSite.mk f))ᵒᵖ) :
    ((spacesStructureSheaf Y).over (spacesEtaleSite.mk f)).obj.obj W ⟶
      ((spacesEtaleLocalizationInverse f).sheafPushforwardContinuous RingCat.{u}
        ((spacesEtaleTopology Y).over (spacesEtaleSite.mk f))
        (spacesEtaleTopology X)).obj (spacesStructureSheaf X) |>.obj.obj W :=
  EtaleRingedTopos.ringExtensionLift X (structureSheaf X)
    (spacesEtaleLocalizationInverseObj f W.unop)
    { pt := (spacesStructureSheaf Y).obj.obj (op W.unop.left)
      π :=
        { app := fun a ↦
            EtaleRingedTopos.ringExtensionEvaluation Y (structureSheaf Y)
              (spacesEtaleLocalizationDiagramObj f W.unop a).hom.unop ≫
            (Modules.restrictStructureMapInv f).hom.app a.right
          naturality := fun _ _ g ↦ spacesEtaleLocalizationHomCone_naturality f W.unop g } }

/-- Postcomposition of a slice arrow over `spacesEtaleRestriction f V` with `V.hom` remains
étale over `X`. -/
instance etale_comp_localization_slice (f : X ⟶ Y) [Etale f] (V : spacesEtaleSite X)
    (a : StructuredArrow (op ((spacesEtaleRestriction f).obj V))
      (smallEtaleToSpaces Y).op) :
    Etale (a.hom.unop.left ≫ V.hom) := by
  have h : (a.hom.unop.left ≫ V.hom) ≫ f = a.right.unop.hom :=
    (Category.assoc a.hom.unop.left V.hom f).trans
      (spacesEtaleLocalization_structuredArrow_w a)
  let W : Over (spacesEtaleSite.mk f) :=
    Over.mk (MorphismProperty.Over.homMk (a.hom.unop.left ≫ V.hom) h :
      (smallEtaleToSpaces Y).obj a.right.unop ⟶ spacesEtaleSite.mk f)
  exact etale_of_spacesEtaleSlice f W

/-- Identity-on-scheme comparison from `restrictPostcompose` of
`smallEtaleSite.mk (a.hom.unop.left ≫ V.hom)` to the original Y-chart `a.right.unop`.
The witness is the structured-arrow triangle
`a.hom.unop.left ≫ ((spacesEtaleRestriction f).obj V).hom = a.right.unop.hom`. -/
private def spacesEtaleLocalizationIsoInvChartIso (f : X ⟶ Y) [Etale f] (V : spacesEtaleSite X)
    (a : StructuredArrow (op ((spacesEtaleRestriction f).obj V))
      (smallEtaleToSpaces Y).op) :
    (Modules.restrictPostcompose f).obj
        (smallEtaleSite.mk (U := a.right.unop.left) (a.hom.unop.left ≫ V.hom)
          (etale_comp_localization_slice f V a)) ≅ a.right.unop :=
  MorphismProperty.CostructuredArrow.isoMk (Iso.refl _) trivial trivial (by
    exact (congrArg (fun k ↦ k ≫ a.right.unop.hom)
      ((ofOverFunctor S).map_id a.right.unop.left)).trans
        ((Category.id_comp _).trans
          ((spacesEtaleLocalization_structuredArrow_w a).symm.trans
            (Category.assoc _ _ _).symm)))

/-- The identity comparison of charts induces the identity on regular functions. -/
private theorem spacesEtaleLocalizationIsoInvChartIso_map (f : X ⟶ Y) [Etale f]
    (V : spacesEtaleSite X)
    (a : StructuredArrow (op ((spacesEtaleRestriction f).obj V))
      (smallEtaleToSpaces Y).op) :
    (structureSheaf Y).obj.map (spacesEtaleLocalizationIsoInvChartIso f V a).inv.op =
      𝟙 _ := by
  change (Scheme.Γ ⋙ forget₂ CommRingCat RingCat).map (𝟙 _) = 𝟙 _
  exact (Scheme.Γ ⋙ forget₂ CommRingCat RingCat).map_id _

/-- The image of a structured arrow over `spacesEtaleRestriction f V` as a structured arrow
over `V`. -/
private def spacesEtaleLocalizationDiagramObjInv (f : X ⟶ Y) [Etale f]
    (V : spacesEtaleSite X)
    (a : StructuredArrow (op ((spacesEtaleRestriction f).obj V))
      (smallEtaleToSpaces Y).op) :
    StructuredArrow (op V) (smallEtaleToSpaces X).op :=
  StructuredArrow.mk
    ((MorphismProperty.Over.homMk a.hom.unop.left rfl :
        (smallEtaleToSpaces X).obj
          (smallEtaleSite.mk (U := a.right.unop.left) (a.hom.unop.left ≫ V.hom)
              (etale_comp_localization_slice f V a)) ⟶ V).op)

set_option backward.isDefEq.respectTransparency false in
/-- Changing the target of an inverse chart commutes with evaluation on regular functions. -/
private theorem spacesEtaleLocalizationDiagramObjInv_naturality (f : X ⟶ Y) [Etale f]
    {V V' : spacesEtaleSite X} (g : V' ⟶ V)
    (a : StructuredArrow (op ((spacesEtaleRestriction f).obj V'))
      (smallEtaleToSpaces Y).op) :
    (spacesStructureSheaf X).obj.map g.op ≫
        EtaleRingedTopos.ringExtensionEvaluation X (structureSheaf X)
          (spacesEtaleLocalizationDiagramObjInv f V' a).hom.unop =
      EtaleRingedTopos.ringExtensionEvaluation X (structureSheaf X)
        (spacesEtaleLocalizationDiagramObjInv f V
          (StructuredArrow.mk (((spacesEtaleRestriction f).map g).op ≫ a.hom))).hom.unop := by
  let b : StructuredArrow (op ((spacesEtaleRestriction f).obj V))
      (smallEtaleToSpaces Y).op :=
    StructuredArrow.mk (((spacesEtaleRestriction f).map g).op ≫ a.hom)
  have h : (ofOverFunctor S).map (𝟙 a.right.unop.left) ≫
      (a.hom.unop.left ≫ V'.hom) = b.hom.unop.left ≫ V.hom :=
    (congrArg (fun k ↦ k ≫ (a.hom.unop.left ≫ V'.hom))
      ((ofOverFunctor S).map_id a.right.unop.left)).trans
      ((Category.id_comp _).trans
        ((congrArg (fun k ↦ a.hom.unop.left ≫ k) (MorphismProperty.Over.w g).symm).trans
          (Category.assoc _ _ _).symm))
  let t : (spacesEtaleLocalizationDiagramObjInv f V b).right.unop ⟶
      (spacesEtaleLocalizationDiagramObjInv f V' a).right.unop :=
    MorphismProperty.CostructuredArrow.homMk (𝟙 _) trivial h
  have ht : (smallEtaleToSpaces X).map t ≫
      ((spacesEtaleLocalizationDiagramObjInv f V' a).hom.unop ≫ g) =
        (spacesEtaleLocalizationDiagramObjInv f V b).hom.unop := by
    apply MorphismProperty.Over.Hom.ext
    exact (congrArg (fun k ↦ k ≫ (a.hom.unop.left ≫ g.left))
      ((ofOverFunctor S).map_id a.right.unop.left)).trans (Category.id_comp _)
  have hm : (structureSheaf X).obj.map t.op = 𝟙 _ := by
    change (Scheme.Γ ⋙ forget₂ CommRingCat RingCat).map (𝟙 _) = 𝟙 _
    exact (Scheme.Γ ⋙ forget₂ CommRingCat RingCat).map_id _
  have he := spacesEtaleLocalizationEvaluation_naturality X (structureSheaf X)
    ((spacesEtaleLocalizationDiagramObjInv f V' a).hom.unop ≫ g)
    (spacesEtaleLocalizationDiagramObjInv f V b).hom.unop t ht
  have he' := he.trans
    ((congrArg (fun k ↦
      EtaleRingedTopos.ringExtensionEvaluation X (structureSheaf X)
        ((spacesEtaleLocalizationDiagramObjInv f V' a).hom.unop ≫ g) ≫ k) hm).trans
      (Category.comp_id _))
  exact (spacesEtaleLocalizationEvaluation_precomp X (structureSheaf X) g
    (spacesEtaleLocalizationDiagramObjInv f V' a).hom.unop).trans he'.symm

set_option backward.isDefEq.respectTransparency false in
/-- The inverse chart evaluations and identity chart comparisons form a cone. -/
private theorem spacesEtaleLocalizationInvCone_naturality (f : X ⟶ Y) [Etale f]
    (V : spacesEtaleSite X)
    {a b : StructuredArrow (op ((spacesEtaleRestriction f).obj V))
      (smallEtaleToSpaces Y).op} (g : a ⟶ b) :
    𝟙 ((spacesStructureSheaf X).obj.obj (op V)) ≫
        (EtaleRingedTopos.ringExtensionEvaluation X (structureSheaf X)
            (spacesEtaleLocalizationDiagramObjInv f V b).hom.unop ≫
          (Modules.restrictStructureMap f).hom.app
            (op (smallEtaleSite.mk (U := b.right.unop.left) (b.hom.unop.left ≫ V.hom)
              (etale_comp_localization_slice f V b))) ≫
          (structureSheaf Y).obj.map (spacesEtaleLocalizationIsoInvChartIso f V b).inv.op) =
      (EtaleRingedTopos.ringExtensionEvaluation X (structureSheaf X)
          (spacesEtaleLocalizationDiagramObjInv f V a).hom.unop ≫
        (Modules.restrictStructureMap f).hom.app
          (op (smallEtaleSite.mk (U := a.right.unop.left) (a.hom.unop.left ≫ V.hom)
            (etale_comp_localization_slice f V a))) ≫
        (structureSheaf Y).obj.map (spacesEtaleLocalizationIsoInvChartIso f V a).inv.op) ≫
        (structureSheaf Y).obj.map g.right := by
  have h : (ofOverFunctor S).map g.right.unop.left ≫
      (a.hom.unop.left ≫ V.hom) = b.hom.unop.left ≫ V.hom :=
    (Category.assoc _ _ _).symm.trans
      (congrArg (fun k : _ ⟶ V.left ↦ k ≫ V.hom)
        (congrArg (fun k ↦ k.unop.left) (StructuredArrow.w g)))
  let t : (spacesEtaleLocalizationDiagramObjInv f V b).right.unop ⟶
      (spacesEtaleLocalizationDiagramObjInv f V a).right.unop :=
    MorphismProperty.CostructuredArrow.homMk g.right.unop.left trivial h
  have ht : (smallEtaleToSpaces X).map t ≫
      (spacesEtaleLocalizationDiagramObjInv f V a).hom.unop =
        (spacesEtaleLocalizationDiagramObjInv f V b).hom.unop := by
    apply MorphismProperty.Over.Hom.ext
    exact congrArg (fun k ↦ k.unop.left) (StructuredArrow.w g)
  have he := spacesEtaleLocalizationEvaluation_naturality X (structureSheaf X)
    _ _ t ht
  dsimp only [Functor.const_obj_obj, Functor.const_obj_map, Functor.comp_obj,
    Functor.comp_map, StructuredArrow.proj_obj, StructuredArrow.proj_map]
  rw [spacesEtaleLocalizationIsoInvChartIso_map f V b,
    spacesEtaleLocalizationIsoInvChartIso_map f V a]
  change 𝟙 _ ≫
      (EtaleRingedTopos.ringExtensionEvaluation X (structureSheaf X)
          (spacesEtaleLocalizationDiagramObjInv f V b).hom.unop ≫ 𝟙 _ ≫ 𝟙 _) =
    (EtaleRingedTopos.ringExtensionEvaluation X (structureSheaf X)
        (spacesEtaleLocalizationDiagramObjInv f V a).hom.unop ≫ 𝟙 _ ≫ 𝟙 _) ≫
      (structureSheaf X).obj.map t.op
  simpa only [Category.id_comp, Category.comp_id] using he

set_option backward.isDefEq.respectTransparency false in
/-- The inverse structure-sheaf component is the lift of chart evaluations and
identity-on-sections restriction, transported along the identity chart comparison. -/
def spacesEtaleLocalizationIsoInvStructureSheaf_app (f : X ⟶ Y) [Etale f]
    (V : (spacesEtaleSite X)ᵒᵖ) :
    (spacesStructureSheaf X).obj.obj V ⟶
      ((spacesEtaleLocalizationFunctor f).sheafPushforwardContinuous RingCat.{u}
        (spacesEtaleTopology X)
        ((spacesEtaleTopology Y).over (spacesEtaleSite.mk f))).obj
        ((spacesStructureSheaf Y).over (spacesEtaleSite.mk f)) |>.obj.obj V :=
  EtaleRingedTopos.ringExtensionLift Y (structureSheaf Y)
    ((spacesEtaleRestriction f).obj V.unop)
    { pt := (spacesStructureSheaf X).obj.obj V
      π :=
        { app := fun a ↦
            EtaleRingedTopos.ringExtensionEvaluation X (structureSheaf X)
              (spacesEtaleLocalizationDiagramObjInv f V.unop a).hom.unop ≫
            (Modules.restrictStructureMap f).hom.app
              (op (smallEtaleSite.mk (U := a.right.unop.left) (a.hom.unop.left ≫ V.unop.hom)
                (etale_comp_localization_slice f V.unop a))) ≫
            (structureSheaf Y).obj.map (spacesEtaleLocalizationIsoInvChartIso f V.unop a).inv.op
          naturality := fun _ _ g ↦ spacesEtaleLocalizationInvCone_naturality f V.unop g } }

set_option backward.isDefEq.respectTransparency false in
/-- Forward structure-sheaf comparison from the restricted structure sheaf of `Y` to the
pushforward of `𝒪` along `spacesEtaleLocalizationInverse`. -/
@[expose]
def spacesEtaleLocalizationIsoHomStructureSheaf (f : X ⟶ Y) [Etale f] :
    (spacesStructureSheaf Y).over (spacesEtaleSite.mk f) ⟶
      ((spacesEtaleLocalizationInverse f).sheafPushforwardContinuous RingCat.{u}
        ((spacesEtaleTopology Y).over (spacesEtaleSite.mk f))
        (spacesEtaleTopology X)).obj (spacesStructureSheaf X) :=
  ⟨{ app := fun W ↦ spacesEtaleLocalizationIsoHomStructureSheaf_app f W
     naturality := by
       intro W W' g
       change (spacesStructureSheaf Y).obj.map g.unop.left.op ≫
           spacesEtaleLocalizationIsoHomStructureSheaf_app f W' =
         spacesEtaleLocalizationIsoHomStructureSheaf_app f W ≫
           (spacesStructureSheaf X).obj.map ((spacesEtaleLocalizationInverse f).map g.unop).op
       dsimp only [spacesEtaleLocalizationIsoHomStructureSheaf_app, spacesStructureSheaf]
       let c (T : Over (spacesEtaleSite.mk f)) :
           Cone (StructuredArrow.proj (op (spacesEtaleLocalizationInverseObj f T))
             (smallEtaleToSpaces X).op ⋙ (structureSheaf X).obj) :=
         { pt := (spacesStructureSheaf Y).obj.obj (op T.left)
           π :=
             { app := fun a ↦ EtaleRingedTopos.ringExtensionEvaluation Y (structureSheaf Y)
                 (spacesEtaleLocalizationDiagramObj f T a).hom.unop ≫
                 (Modules.restrictStructureMapInv f).hom.app a.right
               naturality := fun _ _ g ↦ spacesEtaleLocalizationHomCone_naturality f T g } }
       refine spacesEtaleLocalizationLift_naturality X (structureSheaf X)
         ((spacesEtaleLocalizationInverse f).map g.unop) (c W.unop) (c W'.unop)
         ((spacesStructureSheaf Y).obj.map g.unop.left.op) ?_
       intro a
       change (spacesStructureSheaf Y).obj.map g.unop.left.op ≫
           (EtaleRingedTopos.ringExtensionEvaluation Y (structureSheaf Y)
               (spacesEtaleLocalizationDiagramObj f W'.unop a).hom.unop ≫ 𝟙 _) =
         EtaleRingedTopos.ringExtensionEvaluation Y (structureSheaf Y)
             (spacesEtaleLocalizationDiagramObj f W.unop
               (StructuredArrow.mk
                 (((spacesEtaleLocalizationInverse f).map g.unop).op ≫ a.hom))).hom.unop ≫ 𝟙 _
       simp only [Category.comp_id]
       exact spacesEtaleLocalizationEvaluation_precomp Y (structureSheaf Y) g.unop.left
         (spacesEtaleLocalizationDiagramObj f W'.unop a).hom.unop }⟩

set_option backward.isDefEq.respectTransparency false in
/-- Inverse structure-sheaf comparison from `𝒪` on `X_spaces,étale` to the pushforward of the
restricted structure sheaf of `Y` along `spacesEtaleLocalizationFunctor`. -/
@[expose]
def spacesEtaleLocalizationIsoInvStructureSheaf (f : X ⟶ Y) [Etale f] :
    spacesStructureSheaf X ⟶
      ((spacesEtaleLocalizationFunctor f).sheafPushforwardContinuous RingCat.{u}
        (spacesEtaleTopology X)
        ((spacesEtaleTopology Y).over (spacesEtaleSite.mk f))).obj
        ((spacesStructureSheaf Y).over (spacesEtaleSite.mk f)) :=
  ⟨{ app := fun V ↦ spacesEtaleLocalizationIsoInvStructureSheaf_app f V
     naturality := by
       intro V V' g
       change (spacesStructureSheaf X).obj.map g.unop.op ≫
           spacesEtaleLocalizationIsoInvStructureSheaf_app f V' =
         spacesEtaleLocalizationIsoInvStructureSheaf_app f V ≫
           (spacesStructureSheaf Y).obj.map ((spacesEtaleRestriction f).map g.unop).op
       dsimp only [spacesEtaleLocalizationIsoInvStructureSheaf_app, spacesStructureSheaf]
       let c (T : spacesEtaleSite X) :
           Cone (StructuredArrow.proj (op ((spacesEtaleRestriction f).obj T))
             (smallEtaleToSpaces Y).op ⋙ (structureSheaf Y).obj) :=
         { pt := (spacesStructureSheaf X).obj.obj (op T)
           π :=
             { app := fun a ↦ EtaleRingedTopos.ringExtensionEvaluation X (structureSheaf X)
                 (spacesEtaleLocalizationDiagramObjInv f T a).hom.unop ≫
                 (Modules.restrictStructureMap f).hom.app
                   (op (smallEtaleSite.mk (U := a.right.unop.left) (a.hom.unop.left ≫ T.hom)
                     (etale_comp_localization_slice f T a))) ≫
                 (structureSheaf Y).obj.map (spacesEtaleLocalizationIsoInvChartIso f T a).inv.op
               naturality := fun _ _ g ↦ spacesEtaleLocalizationInvCone_naturality f T g } }
       refine spacesEtaleLocalizationLift_naturality Y (structureSheaf Y)
         ((spacesEtaleRestriction f).map g.unop) (c V.unop) (c V'.unop)
         ((spacesStructureSheaf X).obj.map g.unop.op) ?_
       intro a
       dsimp only [c]
       rw [spacesEtaleLocalizationIsoInvChartIso_map f V'.unop a,
         spacesEtaleLocalizationIsoInvChartIso_map f V.unop
           (StructuredArrow.mk (((spacesEtaleRestriction f).map g.unop).op ≫ a.hom))]
       change (spacesStructureSheaf X).obj.map g.unop.op ≫
           (EtaleRingedTopos.ringExtensionEvaluation X (structureSheaf X)
               (spacesEtaleLocalizationDiagramObjInv f V'.unop a).hom.unop ≫ 𝟙 _ ≫ 𝟙 _) =
         EtaleRingedTopos.ringExtensionEvaluation X (structureSheaf X)
             (spacesEtaleLocalizationDiagramObjInv f V.unop
               (StructuredArrow.mk
                 (((spacesEtaleRestriction f).map g.unop).op ≫ a.hom))).hom.unop ≫ 𝟙 _ ≫ 𝟙 _
       simpa only [Category.comp_id] using
         spacesEtaleLocalizationDiagramObjInv_naturality f g.unop a }⟩

/-- The morphism of ringed sites from `(X_spaces,étale, 𝒪_X)` to the localization of
`(Y_spaces,étale, 𝒪_Y)` at `X`. -/
@[expose]
def spacesEtaleLocalizationIsoHom (f : X ⟶ Y) [Etale f] :
    RingedSiteMap (spacesEtaleTopology X) (spacesStructureSheaf X)
      ((spacesEtaleTopology Y).over (spacesEtaleSite.mk f))
      ((spacesStructureSheaf Y).over (spacesEtaleSite.mk f)) where
  base := spacesEtaleLocalizationInverse f
  isMorphismOfSites := spacesEtaleLocalizationInverse.instIsMorphismOfSites f
  structureSheafMap := spacesEtaleLocalizationIsoHomStructureSheaf f

/-- The morphism of ringed sites from the localization of `(Y_spaces,étale, 𝒪_Y)` at `X` to
`(X_spaces,étale, 𝒪_X)`. -/
@[expose]
def spacesEtaleLocalizationIsoInv (f : X ⟶ Y) [Etale f] :
    RingedSiteMap ((spacesEtaleTopology Y).over (spacesEtaleSite.mk f))
      ((spacesStructureSheaf Y).over (spacesEtaleSite.mk f))
      (spacesEtaleTopology X) (spacesStructureSheaf X) where
  base := spacesEtaleLocalizationFunctor f
  isMorphismOfSites := spacesEtaleLocalizationFunctor.instIsMorphismOfSites f
  structureSheafMap := spacesEtaleLocalizationIsoInvStructureSheaf f

/-- The forward localization map followed by the inverse is the identity on the domain site. -/
theorem spacesEtaleLocalizationIso_hom_inv_id (f : X ⟶ Y) [Etale f] :
    RingedSiteMap.comp (spacesEtaleLocalizationIsoHom f) (spacesEtaleLocalizationIsoInv f) =
      RingedSiteMap.id (spacesEtaleTopology X) (spacesStructureSheaf X) :=
  sorry

/-- The inverse localization map followed by the forward is the identity on the slice site. -/
theorem spacesEtaleLocalizationIso_inv_hom_id (f : X ⟶ Y) [Etale f] :
    RingedSiteMap.comp (spacesEtaleLocalizationIsoInv f) (spacesEtaleLocalizationIsoHom f) =
      RingedSiteMap.id ((spacesEtaleTopology Y).over (spacesEtaleSite.mk f))
        ((spacesStructureSheaf Y).over (spacesEtaleSite.mk f)) :=
  sorry

/-- Identification of spaces-étale ringed sites
`(X_spaces,étale, 𝒪_X) ≅ (Y_spaces,étale / X, 𝒪_Y restricted)` along an étale morphism of
algebraic spaces. -/
@[expose]
def spacesEtaleLocalizationIso (f : X ⟶ Y) [Etale f] :
    RingedSiteMap.Iso (spacesEtaleTopology X) (spacesStructureSheaf X)
      ((spacesEtaleTopology Y).over (spacesEtaleSite.mk f))
      ((spacesStructureSheaf Y).over (spacesEtaleSite.mk f)) where
  hom := spacesEtaleLocalizationIsoHom f
  inv := spacesEtaleLocalizationIsoInv f
  hom_inv_id := spacesEtaleLocalizationIso_hom_inv_id f
  inv_hom_id := spacesEtaleLocalizationIso_inv_hom_id f

/-- The base functor of the forward ringed-site morphism is `spacesEtaleLocalizationInverse`. -/
@[simp]
theorem spacesEtaleLocalizationIso_hom_base (f : X ⟶ Y) [Etale f] :
    (spacesEtaleLocalizationIso f).hom.base = spacesEtaleLocalizationInverse f :=
  rfl

/-- The base functor of the inverse ringed-site morphism is `spacesEtaleLocalizationFunctor`. -/
@[simp]
theorem spacesEtaleLocalizationIso_inv_base (f : X ⟶ Y) [Etale f] :
    (spacesEtaleLocalizationIso f).inv.base = spacesEtaleLocalizationFunctor f :=
  rfl

/-- The forward structure-sheaf comparison at `W` is
`spacesEtaleLocalizationIsoHomStructureSheaf_app`. -/
@[simp]
theorem spacesEtaleLocalizationIso_hom_structureSheaf_app (f : X ⟶ Y) [Etale f]
    (W : (Over (spacesEtaleSite.mk f))ᵒᵖ) :
    ((spacesEtaleLocalizationIso f).hom.structureSheafMap).hom.app W =
      spacesEtaleLocalizationIsoHomStructureSheaf_app f W :=
  rfl

/-- The inverse structure-sheaf comparison at `V` is
`spacesEtaleLocalizationIsoInvStructureSheaf_app`. -/
@[simp]
theorem spacesEtaleLocalizationIso_inv_structureSheaf_app (f : X ⟶ Y) [Etale f]
    (V : (spacesEtaleSite X)ᵒᵖ) :
    ((spacesEtaleLocalizationIso f).inv.structureSheafMap).hom.app V =
      spacesEtaleLocalizationIsoInvStructureSheaf_app f V :=
  rfl


end AlgebraicGeometry.AlgebraicSpace
