/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.RestrictToScheme
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.PresentationRestriction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.IdentityChart

/-!
# Free modules and local presentations for scheme restriction

The coefficient comparison and coproduct inclusions define a map from a free
scheme module to the restriction of the free étale module. Restriction to an
étale chart is also compared with restriction to the corresponding slice site.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules.RestrictToScheme

variable {S : Scheme.{u}}

/-- The coefficient comparison for restriction to the underlying scheme. -/
def unitMap (Z : Over S) :
    SheafOfModules.unit Z.left.ringCatSheaf ⟶
      (Modules.restrictToScheme Z).obj
        (SheafOfModules.unit (structureSheaf (ofOver Z))) :=
  SheafOfModules.unitToPushforwardObjUnit
      (SmallEtale.openChartStructureMap (tautologicalChart Z)) ≫
    (SmallEtale.Modules.toScheme (tautologicalChart Z)).map
      (SheafOfModules.unitToPushforwardObjUnit (toPresentationStructureMap (ofOver Z)))

/-- Restriction sends each basis section of a free module to the same basis section. -/
def freeRestrictionComparison (Z : Over S) (I : Type u) :
    SheafOfModules.free (R := Z.left.ringCatSheaf) I ⟶
      (Modules.restrictToScheme Z).obj
        (SheafOfModules.free (R := structureSheaf (ofOver Z)) I) :=
  SheafOfModules.mapFree (Modules.restrictToScheme Z) I (unitMap Z)

/-- The free comparison is specified by its maps on the coproduct inclusions. -/
@[reassoc (attr := simp)]
theorem ιFree_freeRestrictionComparison (Z : Over S) (I : Type u) (i : I) :
    SheafOfModules.ιFree i ≫ freeRestrictionComparison Z I =
      unitMap Z ≫ (Modules.restrictToScheme Z).map (SheafOfModules.ιFree i) :=
  SheafOfModules.ιFree_mapFree _ _ _ _

/-- The free restriction comparison is natural in its basis index type. -/
@[reassoc]
theorem freeRestrictionComparison_naturality (Z : Over S) {I J : Type u} (f : I → J) :
    SheafOfModules.freeMap f ≫ freeRestrictionComparison Z J =
      freeRestrictionComparison Z I ≫
        (Modules.restrictToScheme Z).map (SheafOfModules.freeMap f) := sorry

private theorem chartToSlice_obj_w {X : AlgebraicSpace S} (U : smallEtaleSite X) (V : smallEtaleSite (ofOver U.left)) :
    ofOverMap (yonedaEquiv V.hom) ≫ U.hom =
      ((Modules.restrictPostcompose U.hom).obj V).hom := sorry

private theorem chartToSlice_map_w {X : AlgebraicSpace S} (U : smallEtaleSite X)
    {V W : smallEtaleSite (ofOver U.left)} (f : V ⟶ W) :
    ofOverMap f.left ≫ ((Modules.restrictPostcompose U.hom).obj W).hom =
      ((Modules.restrictPostcompose U.hom).obj V).hom := sorry

private theorem chartToSlice_map_over_w {X : AlgebraicSpace S} (U : smallEtaleSite X)
    {V W : smallEtaleSite (ofOver U.left)} (f : V ⟶ W) :
    (MorphismProperty.CostructuredArrow.homMk
      (A := (Modules.restrictPostcompose U.hom).obj V)
      (B := (Modules.restrictPostcompose U.hom).obj W) f.left trivial (chartToSlice_map_w U f)) ≫
      (Over.mk (MorphismProperty.CostructuredArrow.homMk
      (B := U) (yonedaEquiv W.hom) trivial (chartToSlice_obj_w U W) :
      (Modules.restrictPostcompose U.hom).obj W ⟶ U)).hom = (Over.mk (MorphismProperty.CostructuredArrow.homMk
      (B := U) (yonedaEquiv V.hom) trivial (chartToSlice_obj_w U V) :
      (Modules.restrictPostcompose U.hom).obj V ⟶ U)).hom := sorry

private theorem chartToSlice_map_id {X : AlgebraicSpace S} (U : smallEtaleSite X) (V : smallEtaleSite (ofOver U.left)) :
    (Over.homMk (MorphismProperty.CostructuredArrow.homMk
      (A := (Modules.restrictPostcompose U.hom).obj V)
      (B := (Modules.restrictPostcompose U.hom).obj V) (𝟙 V : V ⟶ V).left trivial
      (chartToSlice_map_w U (𝟙 V))) (chartToSlice_map_over_w U (𝟙 V)) : (Over.mk (MorphismProperty.CostructuredArrow.homMk
      (B := U) (yonedaEquiv V.hom) trivial (chartToSlice_obj_w U V) :
      (Modules.restrictPostcompose U.hom).obj V ⟶ U)) ⟶ (Over.mk (MorphismProperty.CostructuredArrow.homMk
      (B := U) (yonedaEquiv V.hom) trivial (chartToSlice_obj_w U V) :
      (Modules.restrictPostcompose U.hom).obj V ⟶ U))) = 𝟙 _ := sorry

private theorem chartToSlice_map_comp {X : AlgebraicSpace S} (U : smallEtaleSite X)
    {V W Z : smallEtaleSite (ofOver U.left)} (f : V ⟶ W) (g : W ⟶ Z) :
    (f ≫ g).left = f.left ≫ g.left := sorry

/-- Regard a chart over an étale object as an object of the ambient slice site. -/
@[no_expose]
def chartToSlice {X : AlgebraicSpace S} (U : smallEtaleSite X) :
    smallEtaleSite (ofOver U.left) ⥤ Over U where
  obj V := Over.mk (MorphismProperty.CostructuredArrow.homMk
      (B := U) (yonedaEquiv V.hom) trivial (chartToSlice_obj_w U V) :
      (Modules.restrictPostcompose U.hom).obj V ⟶ U)
  map {V W} f := Over.homMk (MorphismProperty.CostructuredArrow.homMk
      (A := (Modules.restrictPostcompose U.hom).obj V)
      (B := (Modules.restrictPostcompose U.hom).obj W) f.left trivial
      (chartToSlice_map_w U f)) (chartToSlice_map_over_w U f)
  map_id V := chartToSlice_map_id U V
  map_comp f g := by
    apply Over.OverMorphism.ext
    apply MorphismProperty.CostructuredArrow.Hom.ext
    exact chartToSlice_map_comp U f g

private theorem sliceToChart_map_w {X : AlgebraicSpace S} (U : smallEtaleSite X) {V W : Over U} (f : V ⟶ W) :
    ofOverMap f.left.left ≫ ofOverMap W.hom.left = ofOverMap V.hom.left := sorry

private theorem sliceToChart_map_id {X : AlgebraicSpace S} (U : smallEtaleSite X) (V : Over U) :
    (MorphismProperty.CostructuredArrow.homMk (A := smallEtaleSite.mk (ofOverMap V.hom.left) (SmallEtaleGlueing.etale_siteHom V.hom)) (B := smallEtaleSite.mk (ofOverMap V.hom.left) (SmallEtaleGlueing.etale_siteHom V.hom)) (𝟙 V : V ⟶ V).left.left trivial (sliceToChart_map_w U (𝟙 V)) : (smallEtaleSite.mk (ofOverMap V.hom.left) (SmallEtaleGlueing.etale_siteHom V.hom)) ⟶ (smallEtaleSite.mk (ofOverMap V.hom.left) (SmallEtaleGlueing.etale_siteHom V.hom))) = 𝟙 _ := sorry

private theorem sliceToChart_map_comp {X : AlgebraicSpace S} (U : smallEtaleSite X) {V W Z : Over U}
    (f : V ⟶ W) (g : W ⟶ Z) :
    (MorphismProperty.CostructuredArrow.homMk (A := smallEtaleSite.mk (ofOverMap V.hom.left) (SmallEtaleGlueing.etale_siteHom V.hom)) (B := smallEtaleSite.mk (ofOverMap Z.hom.left) (SmallEtaleGlueing.etale_siteHom Z.hom)) (f ≫ g : V ⟶ Z).left.left trivial (sliceToChart_map_w U (f ≫ g)) : (smallEtaleSite.mk (ofOverMap V.hom.left) (SmallEtaleGlueing.etale_siteHom V.hom)) ⟶ (smallEtaleSite.mk (ofOverMap Z.hom.left) (SmallEtaleGlueing.etale_siteHom Z.hom))) =
      (MorphismProperty.CostructuredArrow.homMk (A := smallEtaleSite.mk (ofOverMap V.hom.left) (SmallEtaleGlueing.etale_siteHom V.hom)) (B := smallEtaleSite.mk (ofOverMap W.hom.left) (SmallEtaleGlueing.etale_siteHom W.hom)) f.left.left trivial (sliceToChart_map_w U f)) ≫ (MorphismProperty.CostructuredArrow.homMk (A := smallEtaleSite.mk (ofOverMap W.hom.left) (SmallEtaleGlueing.etale_siteHom W.hom)) (B := smallEtaleSite.mk (ofOverMap Z.hom.left) (SmallEtaleGlueing.etale_siteHom Z.hom)) g.left.left trivial (sliceToChart_map_w U g)) := sorry

/-- Recover a represented chart from an arrow in the slice site. -/
@[no_expose]
def sliceToChart {X : AlgebraicSpace S} (U : smallEtaleSite X) :
    Over U ⥤ smallEtaleSite (ofOver U.left) where
  obj V := smallEtaleSite.mk (ofOverMap V.hom.left) (SmallEtaleGlueing.etale_siteHom V.hom)
  map {V W} f := MorphismProperty.CostructuredArrow.homMk (A := smallEtaleSite.mk (ofOverMap V.hom.left) (SmallEtaleGlueing.etale_siteHom V.hom)) (B := smallEtaleSite.mk (ofOverMap W.hom.left) (SmallEtaleGlueing.etale_siteHom W.hom)) f.left.left trivial (sliceToChart_map_w U f)
  map_id V := sliceToChart_map_id U V
  map_comp f g := sliceToChart_map_comp U f g

private theorem chartSliceUnit_hom_w {X : AlgebraicSpace S} (U : smallEtaleSite X) (V : smallEtaleSite (ofOver U.left)) :
    ofOverMap (𝟙 V.left) ≫ ((chartToSlice U ⋙ sliceToChart U).obj V).hom = ((𝟭 (smallEtaleSite (ofOver U.left))).obj V).hom := sorry

private theorem chartSliceUnit_inv_w {X : AlgebraicSpace S} (U : smallEtaleSite X) (V : smallEtaleSite (ofOver U.left)) :
    ofOverMap (𝟙 V.left) ≫ ((𝟭 (smallEtaleSite (ofOver U.left))).obj V).hom = ((chartToSlice U ⋙ sliceToChart U).obj V).hom := sorry

private theorem chartSliceUnit_hom_inv_id {X : AlgebraicSpace S} (U : smallEtaleSite X) (V : smallEtaleSite (ofOver U.left)) :
    (MorphismProperty.CostructuredArrow.homMk (A := V) (B := (chartToSlice U ⋙ sliceToChart U).obj V) (𝟙 V.left) trivial (chartSliceUnit_hom_w U V) : (𝟭 (smallEtaleSite (ofOver U.left))).obj V ⟶ (chartToSlice U ⋙ sliceToChart U).obj V) ≫ (MorphismProperty.CostructuredArrow.homMk (A := (chartToSlice U ⋙ sliceToChart U).obj V) (B := V) (𝟙 V.left) trivial (chartSliceUnit_inv_w U V)) = 𝟙 _ := sorry

private theorem chartSliceUnit_inv_hom_id {X : AlgebraicSpace S} (U : smallEtaleSite X) (V : smallEtaleSite (ofOver U.left)) :
    (MorphismProperty.CostructuredArrow.homMk (A := (chartToSlice U ⋙ sliceToChart U).obj V) (B := V) (𝟙 V.left) trivial (chartSliceUnit_inv_w U V) : (chartToSlice U ⋙ sliceToChart U).obj V ⟶ (𝟭 (smallEtaleSite (ofOver U.left))).obj V) ≫ (MorphismProperty.CostructuredArrow.homMk (A := V) (B := (chartToSlice U ⋙ sliceToChart U).obj V) (𝟙 V.left) trivial (chartSliceUnit_hom_w U V)) = 𝟙 _ := sorry

private theorem chartSliceUnit_naturality {X : AlgebraicSpace S} (U : smallEtaleSite X) {V W : smallEtaleSite (ofOver U.left)} (f : V ⟶ W) :
    (𝟭 (smallEtaleSite (ofOver U.left))).map f ≫ (MorphismProperty.CostructuredArrow.homMk (A := W) (B := (chartToSlice U ⋙ sliceToChart U).obj W) (𝟙 W.left) trivial (chartSliceUnit_hom_w U W)) =
      (MorphismProperty.CostructuredArrow.homMk (A := V) (B := (chartToSlice U ⋙ sliceToChart U).obj V) (𝟙 V.left) trivial (chartSliceUnit_hom_w U V)) ≫ (chartToSlice U ⋙ sliceToChart U).map f := sorry

/-- Reconstruction of a chart preserves its underlying represented scheme. -/
@[no_expose]
def chartSliceUnitIso {X : AlgebraicSpace S} (U : smallEtaleSite X) : 𝟭 (smallEtaleSite (ofOver U.left)) ≅ chartToSlice U ⋙ sliceToChart U :=
  NatIso.ofComponents (fun V ↦
    { hom := MorphismProperty.CostructuredArrow.homMk (A := V) (B := (chartToSlice U ⋙ sliceToChart U).obj V) (𝟙 V.left) trivial (chartSliceUnit_hom_w U V)
      inv := MorphismProperty.CostructuredArrow.homMk (A := (chartToSlice U ⋙ sliceToChart U).obj V) (B := V) (𝟙 V.left) trivial (chartSliceUnit_inv_w U V)
      hom_inv_id := chartSliceUnit_hom_inv_id U V
      inv_hom_id := chartSliceUnit_inv_hom_id U V })
    (fun f ↦ chartSliceUnit_naturality U f)

private theorem chartSliceCounit_hom_w {X : AlgebraicSpace S} (U : smallEtaleSite X) (V : Over U) :
    ofOverMap (𝟙 V.left.left) ≫ V.left.hom = ((sliceToChart U ⋙ chartToSlice U).obj V).left.hom := sorry

private theorem chartSliceCounit_inv_w {X : AlgebraicSpace S} (U : smallEtaleSite X) (V : Over U) :
    ofOverMap (𝟙 V.left.left) ≫ ((sliceToChart U ⋙ chartToSlice U).obj V).left.hom = V.left.hom := sorry

private theorem chartSliceCounit_hom_over_w {X : AlgebraicSpace S} (U : smallEtaleSite X) (V : Over U) :
    (MorphismProperty.CostructuredArrow.homMk (A := ((sliceToChart U ⋙ chartToSlice U).obj V).left) (B := V.left) (𝟙 V.left.left) trivial (chartSliceCounit_hom_w U V)) ≫ V.hom = ((sliceToChart U ⋙ chartToSlice U).obj V).hom := sorry

private theorem chartSliceCounit_inv_over_w {X : AlgebraicSpace S} (U : smallEtaleSite X) (V : Over U) :
    (MorphismProperty.CostructuredArrow.homMk (A := V.left) (B := ((sliceToChart U ⋙ chartToSlice U).obj V).left) (𝟙 V.left.left) trivial (chartSliceCounit_inv_w U V)) ≫ ((sliceToChart U ⋙ chartToSlice U).obj V).hom = V.hom := sorry

private theorem chartSliceCounit_hom_inv_id {X : AlgebraicSpace S} (U : smallEtaleSite X) (V : Over U) :
    (Over.homMk (MorphismProperty.CostructuredArrow.homMk (A := ((sliceToChart U ⋙ chartToSlice U).obj V).left) (B := V.left) (𝟙 V.left.left) trivial (chartSliceCounit_hom_w U V)) (chartSliceCounit_hom_over_w U V) : (sliceToChart U ⋙ chartToSlice U).obj V ⟶ (𝟭 (Over U)).obj V) ≫ (Over.homMk (MorphismProperty.CostructuredArrow.homMk (A := V.left) (B := ((sliceToChart U ⋙ chartToSlice U).obj V).left) (𝟙 V.left.left) trivial (chartSliceCounit_inv_w U V)) (chartSliceCounit_inv_over_w U V)) = 𝟙 _ := sorry

private theorem chartSliceCounit_inv_hom_id {X : AlgebraicSpace S} (U : smallEtaleSite X) (V : Over U) :
    (Over.homMk (MorphismProperty.CostructuredArrow.homMk (A := V.left) (B := ((sliceToChart U ⋙ chartToSlice U).obj V).left) (𝟙 V.left.left) trivial (chartSliceCounit_inv_w U V)) (chartSliceCounit_inv_over_w U V) : (𝟭 (Over U)).obj V ⟶ (sliceToChart U ⋙ chartToSlice U).obj V) ≫ (Over.homMk (MorphismProperty.CostructuredArrow.homMk (A := ((sliceToChart U ⋙ chartToSlice U).obj V).left) (B := V.left) (𝟙 V.left.left) trivial (chartSliceCounit_hom_w U V)) (chartSliceCounit_hom_over_w U V)) = 𝟙 _ := sorry

private theorem chartSliceCounit_naturality {X : AlgebraicSpace S} (U : smallEtaleSite X) {V W : Over U} (f : V ⟶ W) :
    (sliceToChart U ⋙ chartToSlice U).map f ≫ (Over.homMk (MorphismProperty.CostructuredArrow.homMk (A := ((sliceToChart U ⋙ chartToSlice U).obj W).left) (B := W.left) (𝟙 W.left.left) trivial (chartSliceCounit_hom_w U W)) (chartSliceCounit_hom_over_w U W)) =
      (Over.homMk (MorphismProperty.CostructuredArrow.homMk (A := ((sliceToChart U ⋙ chartToSlice U).obj V).left) (B := V.left) (𝟙 V.left.left) trivial (chartSliceCounit_hom_w U V)) (chartSliceCounit_hom_over_w U V)) ≫ (𝟭 (Over U)).map f := sorry

/-- Reconstruction of a slice object preserves its underlying represented scheme. -/
@[no_expose]
def chartSliceCounitIso {X : AlgebraicSpace S} (U : smallEtaleSite X) : sliceToChart U ⋙ chartToSlice U ≅ 𝟭 (Over U) :=
  NatIso.ofComponents (fun V ↦
    { hom := Over.homMk (MorphismProperty.CostructuredArrow.homMk (A := ((sliceToChart U ⋙ chartToSlice U).obj V).left) (B := V.left) (𝟙 V.left.left) trivial (chartSliceCounit_hom_w U V)) (chartSliceCounit_hom_over_w U V)
      inv := Over.homMk (MorphismProperty.CostructuredArrow.homMk (A := V.left) (B := ((sliceToChart U ⋙ chartToSlice U).obj V).left) (𝟙 V.left.left) trivial (chartSliceCounit_inv_w U V)) (chartSliceCounit_inv_over_w U V)
      hom_inv_id := chartSliceCounit_hom_inv_id U V
      inv_hom_id := chartSliceCounit_inv_hom_id U V })
    (fun f ↦ chartSliceCounit_naturality U f)

/-- The étale site of a represented chart is the slice of the ambient étale site. -/
def chartSliceEquivalence {X : AlgebraicSpace S} (U : smallEtaleSite X) :
    smallEtaleSite (ofOver U.left) ≌ Over U :=
  CategoryTheory.Equivalence.mk (chartToSlice U) (sliceToChart U)
    (chartSliceUnitIso U) (chartSliceCounitIso U)

/-- The site equivalence uses the displayed inverse functor. -/
instance chartToSlice_isEquivalence {X : AlgebraicSpace S} (U : smallEtaleSite X) :
    (chartToSlice U).IsEquivalence :=
  (chartSliceEquivalence U).isEquivalence_functor

/-- The chart-to-slice functor preserves the étale sheaf condition. -/
instance chartToSlice_isContinuous {X : AlgebraicSpace S} (U : smallEtaleSite X) :
    (chartToSlice U).IsContinuous (smallEtaleTopology (ofOver U.left))
      ((smallEtaleTopology X).over U) := sorry

/-- The chart-to-slice functor carries the same covering families in both presentations. -/
instance chartToSlice_isCocontinuous {X : AlgebraicSpace S} (U : smallEtaleSite X) :
    (chartToSlice U).IsCocontinuous (smallEtaleTopology (ofOver U.left))
      ((smallEtaleTopology X).over U) := sorry

private theorem sliceStructureHom_naturality {X : AlgebraicSpace S} (U : smallEtaleSite X)
    {V W : (smallEtaleSite (ofOver U.left))ᵒᵖ} (f : V ⟶ W) :
    (structureSheaf (ofOver U.left)).obj.map f ≫ 𝟙 _ = 𝟙 _ ≫ (((chartToSlice U).sheafPushforwardContinuous RingCat.{u}
      (smallEtaleTopology (ofOver U.left)) ((smallEtaleTopology X).over U)).obj
        ((structureSheaf X).over U)).obj.map f := sorry

private theorem sliceStructureInv_naturality {X : AlgebraicSpace S} (U : smallEtaleSite X)
    {V W : (smallEtaleSite (ofOver U.left))ᵒᵖ} (f : V ⟶ W) :
    (((chartToSlice U).sheafPushforwardContinuous RingCat.{u}
      (smallEtaleTopology (ofOver U.left)) ((smallEtaleTopology X).over U)).obj
        ((structureSheaf X).over U)).obj.map f ≫ 𝟙 _ = 𝟙 _ ≫ (structureSheaf (ofOver U.left)).obj.map f := sorry

private theorem sliceStructure_hom_inv_id {X : AlgebraicSpace S} (U : smallEtaleSite X)
    (V : (smallEtaleSite (ofOver U.left))ᵒᵖ) :
    (𝟙 ((structureSheaf (ofOver U.left)).obj.obj V)) ≫ 𝟙 _ = 𝟙 _ := sorry

private theorem sliceStructure_inv_hom_id {X : AlgebraicSpace S} (U : smallEtaleSite X)
    (V : (smallEtaleSite (ofOver U.left))ᵒᵖ) :
    (𝟙 ((((chartToSlice U).sheafPushforwardContinuous RingCat.{u}
      (smallEtaleTopology (ofOver U.left)) ((smallEtaleTopology X).over U)).obj
        ((structureSheaf X).over U)).obj.obj V)) ≫ 𝟙 _ = 𝟙 _ := sorry

/-- The slice and represented structure sheaves have the same section values. -/
@[no_expose]
def sliceStructureIso {X : AlgebraicSpace S} (U : smallEtaleSite X) :
    structureSheaf (ofOver U.left) ≅ ((chartToSlice U).sheafPushforwardContinuous RingCat.{u}
      (smallEtaleTopology (ofOver U.left)) ((smallEtaleTopology X).over U)).obj
        ((structureSheaf X).over U) where
  hom := ⟨{ app := fun _ ↦ 𝟙 _, naturality := fun _ _ f ↦ sliceStructureHom_naturality U f }⟩
  inv := ⟨{ app := fun _ ↦ 𝟙 _, naturality := fun _ _ f ↦ sliceStructureInv_naturality U f }⟩
  hom_inv_id := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    exact sliceStructure_hom_inv_id U V
  inv_hom_id := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    exact sliceStructure_inv_hom_id U V

/-- Convert a module on the slice site into a module on the represented chart. -/
def sliceModules {X : AlgebraicSpace S} (U : smallEtaleSite X) :
    SheafOfModules.{u} ((structureSheaf X).over U) ⥤ (ofOver U.left).Modules :=
  SheafOfModules.pushforward (sliceStructureIso U).hom

/-- The displayed site and ring equivalences make slice conversion a left adjoint. -/
instance sliceModules_isLeftAdjoint {X : AlgebraicSpace S} (U : smallEtaleSite X) :
    (sliceModules U).IsLeftAdjoint :=
  SheafOfModules.isLeftAdjoint_pushforward_of_isIso (sliceStructureIso U).hom

/-- The structure module is unchanged by converting the slice presentation. -/
@[no_expose]
def sliceModulesUnitIso {X : AlgebraicSpace S} (U : smallEtaleSite X) :
    SheafOfModules.unit (structureSheaf (ofOver U.left)) ≅
      (sliceModules U).obj (SheafOfModules.unit ((structureSheaf X).over U)) :=
  CategoryTheory.eqToIso rfl

private theorem sliceRestrictionHom_naturality {X : AlgebraicSpace S} (U : smallEtaleSite X) (M : X.Modules)
    {V W : (smallEtaleSite (ofOver U.left))ᵒᵖ} (f : V ⟶ W) :
    (((SheafOfModules.overFunctor (structureSheaf X) U ⋙ sliceModules U)).obj M).val.map f ≫ 𝟙 _ =
      𝟙 _ ≫ (((@Modules.restrictFunctor S (ofOver U.left) X U.hom U.prop)).obj M).val.map f := sorry

private theorem sliceRestrictionInv_naturality {X : AlgebraicSpace S} (U : smallEtaleSite X) (M : X.Modules)
    {V W : (smallEtaleSite (ofOver U.left))ᵒᵖ} (f : V ⟶ W) :
    (((@Modules.restrictFunctor S (ofOver U.left) X U.hom U.prop)).obj M).val.map f ≫ 𝟙 _ =
      𝟙 _ ≫ (((SheafOfModules.overFunctor (structureSheaf X) U ⋙ sliceModules U)).obj M).val.map f := sorry

private theorem sliceRestriction_hom_inv_id {X : AlgebraicSpace S} (U : smallEtaleSite X) (M : X.Modules)
    (V : (smallEtaleSite (ofOver U.left))ᵒᵖ) :
    (𝟙 ((((SheafOfModules.overFunctor (structureSheaf X) U ⋙ sliceModules U)).obj M).val.obj V)) ≫ 𝟙 _ = 𝟙 _ := sorry

private theorem sliceRestriction_inv_hom_id {X : AlgebraicSpace S} (U : smallEtaleSite X) (M : X.Modules)
    (V : (smallEtaleSite (ofOver U.left))ᵒᵖ) :
    (𝟙 ((((@Modules.restrictFunctor S (ofOver U.left) X U.hom U.prop)).obj M).val.obj V)) ≫ 𝟙 _ = 𝟙 _ := sorry

private theorem sliceRestriction_naturality {X : AlgebraicSpace S} (U : smallEtaleSite X) {M N : X.Modules} (f : M ⟶ N)
    (V : (smallEtaleSite (ofOver U.left))ᵒᵖ) :
    (((SheafOfModules.overFunctor (structureSheaf X) U ⋙ sliceModules U)).map f).val.app V ≫ 𝟙 _ = 𝟙 _ ≫ (((@Modules.restrictFunctor S (ofOver U.left) X U.hom U.prop)).map f).val.app V := sorry

/-- Slice restriction and restriction to its represented chart preserve every section. -/
@[no_expose]
def sliceRestrictionIso {X : AlgebraicSpace S} (U : smallEtaleSite X) : (SheafOfModules.overFunctor (structureSheaf X) U ⋙ sliceModules U) ≅ (@Modules.restrictFunctor S (ofOver U.left) X U.hom U.prop) :=
  NatIso.ofComponents (fun M ↦
    { hom := { val := {
          app := fun _ ↦ 𝟙 _
          naturality := fun f ↦ sliceRestrictionHom_naturality U M f } }
      inv := { val := {
          app := fun _ ↦ 𝟙 _
          naturality := fun f ↦ sliceRestrictionInv_naturality U M f } }
      hom_inv_id := by
        apply SheafOfModules.hom_ext
        apply PresheafOfModules.hom_ext
        intro V
        exact sliceRestriction_hom_inv_id U M V
      inv_hom_id := by
        apply SheafOfModules.hom_ext
        apply PresheafOfModules.hom_ext
        intro V
        exact sliceRestriction_inv_hom_id U M V })
    (fun f ↦ by
      apply SheafOfModules.hom_ext
      apply PresheafOfModules.hom_ext
      intro V
      exact sliceRestriction_naturality U f V)

/-- Transfer a supplied slice presentation to the small étale site of its chart.
The slice sheafification hypothesis is used by the native presentation constructor. -/
def chartPresentation {X : AlgebraicSpace S} (M : X.Modules)
    (U : smallEtaleSite X)
    [HasSheafify ((smallEtaleTopology X).over U) AddCommGrpCat.{u}]
    (P : (M.over U).Presentation) :
    ((@Modules.restrictFunctor S (ofOver U.left) X U.hom U.prop).obj M).Presentation :=
  (P.map (sliceModules U) (sliceModulesUnitIso U)).ofIsIso
    ((sliceRestrictionIso U).hom.app M)

/-- Converting the slice presentation preserves its generator index type. -/
@[simp]
theorem chartPresentation_generators_I {X : AlgebraicSpace S} (M : X.Modules)
    (U : smallEtaleSite X)
    [HasSheafify ((smallEtaleTopology X).over U) AddCommGrpCat.{u}]
    (P : (M.over U).Presentation) :
    (chartPresentation M U P).generators.I = P.generators.I := rfl

/-- Converting the slice presentation preserves its relation index type. -/
@[simp]
theorem chartPresentation_relations_I {X : AlgebraicSpace S} (M : X.Modules)
    (U : smallEtaleSite X)
    [HasSheafify ((smallEtaleTopology X).over U) AddCommGrpCat.{u}]
    (P : (M.over U).Presentation) :
    (chartPresentation M U P).relations.I = P.relations.I := rfl

end AlgebraicGeometry.AlgebraicSpace.Modules.RestrictToScheme
