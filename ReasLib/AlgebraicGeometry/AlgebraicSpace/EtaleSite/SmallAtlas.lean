/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Atlas.Input
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Presentation
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.InducedCategory
public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology

/-! # An explicit small affine-étale atlas site below module pullback

Charts use actual scheme arrows and the supplied atlas map. No module
restriction, selected inverse image, or meromorphic owner is imported.
-/

@[expose] public section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.PullbackFactory.SmallAtlas

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
    (U : Over S) (a : ofOver U ⟶ X) [AlgebraicSpace.Etale a]

def schemeObject (W : U.left.Etale) : Over S := Over.mk (W.hom ≫ U.hom)

def schemeArrow (W : U.left.Etale) : schemeObject U W ⟶ U :=
  Over.homMk W.hom rfl

/-- The actual chart composite is étale; no new chart data are selected. -/
theorem chart_etale (W : U.left.Etale) :
    AlgebraicSpace.Etale ((ofOverFunctor S).map (schemeArrow U W) ≫ a) := by
  letI : (MorphismProperty.over (@AlgebraicGeometry.Etale) :
      MorphismProperty (Over S)).IsStableUnderComposition := by
    rw [MorphismProperty.over_eq_inverseImage]
    infer_instance
  letI : (MorphismProperty.over (@AlgebraicGeometry.Etale) :
      MorphismProperty (Over S)).IsStableUnderBaseChange :=
    ⟨fun square etaleMap ↦ MorphismProperty.of_isPullback (P := @AlgebraicGeometry.Etale)
      (square.map (Over.forget S)) etaleMap⟩
  have hmap : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf
      (yoneda.map (schemeArrow U W)) :=
    MorphismProperty.relative_map (F := yoneda) W.prop
  refine ⟨fun testMap testEtale ↦ ?_⟩
  exact (inferInstance : AlgebraicSpace.Etale a).of_etale _
    ((MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf.comp_mem _ _ testEtale hmap)

def chart (W : U.left.Etale) : smallEtaleSite X :=
  smallEtaleSite.mk ((ofOverFunctor S).map (schemeArrow U W) ≫ a) (chart_etale U a W)

def schemeArrowMap {W W' : U.left.Etale} (f : W ⟶ W') :
    schemeObject U W ⟶ schemeObject U W' :=
  Over.homMk f.left (by
    have hf : f.left ≫ W'.hom = W.hom := by
      simpa using f.w
    change f.left ≫ (W'.hom ≫ U.hom) = W.hom ≫ U.hom
    exact (Category.assoc _ _ _).symm.trans (congrArg (fun schemeMap ↦ schemeMap ≫ U.hom) hf))

def etaleCharts : U.left.Etale ⥤ smallEtaleSite X where
  obj := chart U a
  map {W W'} f := MorphismProperty.CostructuredArrow.homMk (schemeArrowMap U f) trivial (by
    change (ofOverFunctor S).map (schemeArrowMap U f) ≫
      ((ofOverFunctor S).map (schemeArrow U W') ≫ a) =
        (ofOverFunctor S).map (schemeArrow U W) ≫ a
    rw [← Category.assoc, ← Functor.map_comp]
    congr 2
    ext : 1
    change f.left ≫ W'.hom = W.hom
    simpa using f.w)
  map_id _ := by apply MorphismProperty.CostructuredArrow.Hom.ext; rfl
  map_comp _ _ := by apply MorphismProperty.CostructuredArrow.Hom.ext; rfl

def charts : U.left.AffineEtale ⥤ smallEtaleSite X :=
  Scheme.AffineEtale.Spec U.left ⋙ etaleCharts U a

theorem charts_essentiallySmall : EssentiallySmall.{u} U.left.AffineEtale := by infer_instance

def Index : Type u := @SmallModel.{u} U.left.AffineEtale _ (charts_essentiallySmall U)

def object (i : Index U) : smallEtaleSite X :=
  (charts U a).obj ((equivSmallModel U.left.AffineEtale).inverse.obj i)

abbrev Site := InducedCategory (smallEtaleSite X) (object U a)
def inclusion : Site U a ⥤ smallEtaleSite X := inducedFunctor (object U a)

instance inclusion_full : (inclusion U a).Full := InducedCategory.full _
instance inclusion_faithful : (inclusion U a).Faithful := InducedCategory.faithful _

def topology : GrothendieckTopology (Site U a) :=
  (inclusion U a).inducedTopology (smallEtaleTopology X)

set_option backward.isDefEq.respectTransparency false in
private theorem atlas_representableEtale : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a := by
  have identityTest := (inferInstance : AlgebraicSpace.Etale a).of_etale
    (𝟙 (yoneda.obj U)) (AlgebraicSpace.ofOver_id_presheaf_etale U)
  change (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf
    ((𝟙 (yoneda.obj U)) ≫ (a : yoneda.obj U ⟶ X.functorOfPoints)) at identityTest
  rw [Category.id_comp] at identityTest
  exact identityTest

set_option backward.isDefEq.respectTransparency false in
private theorem projection_surjective
    (ha : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) a)
    (chartObject : AlgebraicSpace.smallEtaleSite X) :
    Function.Surjective (((atlas_representableEtale U a).rep.snd chartObject.hom).left) := by
  let representedAtlas := atlas_representableEtale U a
  letI := ha
  have imageCover := Presheaf.imageSieve_mem (Scheme.etaleTopology.over S) a
    (yonedaEquiv chartObject.hom)
  obtain ⟨cover, coverOver, coverInImage⟩ :=
    (Scheme.mem_overGrothendieckTopology (P := @AlgebraicGeometry.Etale)
      chartObject.left (Presheaf.imageSieve a (yonedaEquiv chartObject.hom))).mp imageCover
  letI := coverOver
  intro point
  obtain ⟨index, coverPoint, pointEquality⟩ := cover.exists_eq point
  obtain ⟨localMap, localEquality⟩ := coverInImage _ ((cover.f index).asOver S) ⟨index⟩
  have square : yoneda.map localMap ≫ a =
      yoneda.map ((cover.f index).asOver S) ≫ chartObject.hom := by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map, ← yonedaEquiv_naturality]
    exact localEquality
  let liftMap := representedAtlas.rep.lift' localMap ((cover.f index).asOver S) square
  refine ⟨liftMap.left coverPoint, ?_⟩
  have projectionEquality := congrArg (fun schemeMap ↦ schemeMap.left)
    (representedAtlas.rep.lift'_snd (g := chartObject.hom) localMap ((cover.f index).asOver S) square)
  exact (congrArg (fun schemeMap ↦ schemeMap coverPoint) projectionEquality).trans pointEquality



set_option backward.isDefEq.respectTransparency false in
private theorem point_covered
    (ha : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) a)
    (chartObject : AlgebraicSpace.smallEtaleSite X) (point : chartObject.left.left) :
    ∃ (index : Index U) (chartMap : object U a index ⟶ chartObject)
      (chartPoint : (object U a index).left.left),
      AlgebraicGeometry.Etale chartMap.left.left ∧ chartMap.left.left chartPoint = point := by
  let representedAtlas := atlas_representableEtale U a
  let pullbackObject := representedAtlas.rep.pullback chartObject.hom
  let toAtlas := representedAtlas.rep.fst' chartObject.hom
  let toChart := representedAtlas.rep.snd chartObject.hom
  have square := representedAtlas.rep.isPullback' chartObject.hom
  letI : AlgebraicSpace.Etale chartObject.hom := chartObject.prop
  let representedChart := atlas_representableEtale chartObject.left chartObject.hom
  letI : AlgebraicGeometry.Etale toChart.left := representedAtlas.property _ _ _ square
  letI : AlgebraicGeometry.Etale toAtlas.left := representedChart.property _ _ _ square.flip
  obtain ⟨pullbackPoint, pullbackPointEquality⟩ := projection_surjective U a ha chartObject point
  obtain ⟨ring, affineMap, affineOpen, affinePoint, affinePointEquality⟩ :=
    Scheme.exists_Spec_apply_eq pullbackPoint
  letI : IsOpenImmersion affineMap := affineOpen
  letI : AlgebraicGeometry.Etale (affineMap ≫ toAtlas.left) := inferInstance
  let affineChart := Scheme.AffineEtale.mk (affineMap ≫ toAtlas.left)
  let affineOver : schemeObject U ((Scheme.AffineEtale.Spec U.left).obj affineChart) ⟶ pullbackObject :=
    Over.homMk affineMap (by
      change affineMap ≫ pullbackObject.hom = (affineMap ≫ toAtlas.left) ≫ U.hom
      rw [Category.assoc, Over.w toAtlas])
  have affineToAtlas : affineOver ≫ toAtlas =
      schemeArrow U ((Scheme.AffineEtale.Spec U.left).obj affineChart) := by
    ext : 1
    rfl
  let mapToChart : (charts U a).obj affineChart ⟶ chartObject :=
    MorphismProperty.CostructuredArrow.homMk (affineOver ≫ toChart) trivial (by
      change yoneda.map (affineOver ≫ toChart) ≫ chartObject.hom =
        yoneda.map (schemeArrow U ((Scheme.AffineEtale.Spec U.left).obj affineChart)) ≫ a
      rw [yoneda.map_comp, Category.assoc, ← square.w, ← Category.assoc,
        ← yoneda.map_comp, affineToAtlas])
  let smallEquivalence := equivSmallModel U.left.AffineEtale
  let index := smallEquivalence.functor.obj affineChart
  let chartIso : (charts U a).obj affineChart ≅ object U a index :=
    (charts U a).mapIso (smallEquivalence.unitIso.app affineChart)
  let finalMap := chartIso.inv ≫ mapToChart
  letI : IsIso chartIso.inv.left.left :=
    inferInstanceAs (IsIso ((AlgebraicSpace.smallEtaleToScheme X).map chartIso.inv))
  letI : AlgebraicGeometry.Etale mapToChart.left.left :=
    inferInstanceAs (AlgebraicGeometry.Etale (affineMap ≫ toChart.left))
  refine ⟨index, finalMap, chartIso.hom.left.left affinePoint, ?_, ?_⟩
  · exact inferInstanceAs (AlgebraicGeometry.Etale (chartIso.inv.left.left ≫ mapToChart.left.left))
  · change (chartIso.hom ≫ (chartIso.inv ≫ mapToChart)).left.left affinePoint = point
    rw [chartIso.hom_inv_id_assoc]
    change toChart.left (affineMap affinePoint) = point
    rw [affinePointEquality]
    exact pullbackPointEquality


set_option backward.isDefEq.respectTransparency false in
/-- Affine opens of the atlas pullback cover every chart. The covering family is
transported through the proved small model, with its actual scheme maps. -/
theorem inclusion_coverDense
    (ha : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) a) : (inclusion U a).IsCoverDense (AlgebraicSpace.smallEtaleTopology X) := by
  constructor
  intro chartObject
  let familyIndex := Σ index : Index U,
    {chartMap : object U a index ⟶ chartObject // AlgebraicGeometry.Etale chartMap.left.left}
  let familyObject := fun entry : familyIndex ↦ object U a entry.1
  let familyMap := fun entry : familyIndex ↦ entry.2.val
  letI : chartObject.left.left.Over S := ⟨chartObject.left.hom⟩
  letI (entry : familyIndex) : (familyObject entry).left.left.Over S := ⟨(familyObject entry).left.hom⟩
  letI (entry : familyIndex) : (familyMap entry).left.left.IsOver S :=
    ⟨(familyMap entry).left.w⟩
  let schemeCover : Scheme.Cover.{u} (Scheme.precoverage (@AlgebraicGeometry.Etale)) chartObject.left.left :=
    Scheme.Cover.mkOfCovers familyIndex
      (fun entry ↦ (familyObject entry).left.left) (fun entry ↦ (familyMap entry).left.left)
      (by
        intro point
        obtain ⟨index, chartMap, chartPoint, mapEtale, pointEquality⟩ :=
          point_covered U a ha chartObject point
        exact ⟨⟨index, chartMap, mapEtale⟩, chartPoint, pointEquality⟩)
      (fun entry ↦ entry.2.property)
  letI : Scheme.Cover.Over S schemeCover := {
    over := fun entry ↦ inferInstanceAs ((familyObject entry).left.left.Over S)
    isOver_map := fun entry ↦ inferInstanceAs ((familyMap entry).left.left.IsOver S) }
  have coverMem : Presieve.ofArrows familyObject familyMap ∈
      AlgebraicSpace.smallEtalePrecoverage X chartObject := by
    change (Presieve.ofArrows familyObject familyMap).map (AlgebraicSpace.smallEtaleToOver X) ∈
      (Scheme.overPretopology (@AlgebraicGeometry.Etale) S).toPrecoverage chartObject.left
    refine ⟨schemeCover, inferInstance, ?_⟩
    rw [Presieve.map_ofArrows]
    rfl
  apply (AlgebraicSpace.smallEtaleTopology X).superset_covering _
    (Precoverage.generate_mem_toGrothendieck coverMem)
  apply (Sieve.generate_le_iff _ _).2
  intro sourceObject chartMap chartMapMem
  cases chartMapMem with
  | mk entry => exact Presieve.in_coverByImage (inclusion U a) (familyMap entry)

theorem denseSubsite
    (ha : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) a) :
    (inclusion U a).IsDenseSubsite (topology U a) (smallEtaleTopology X) := by
  -- Local instance justification (proof-local temporary data): Use the cover-density proved for the supplied etale atlas a to obtain the induced-topology dense-subsite law.
  letI := inclusion_coverDense U a ha
  change (inclusion U a).IsDenseSubsite
    ((inclusion U a).inducedTopology (smallEtaleTopology X)) (smallEtaleTopology X)
  infer_instance

end AlgebraicGeometry.AlgebraicSpace.PullbackFactory.SmallAtlas

namespace AlgebraicGeometry.AlgebraicSpace.AtlasInput

variable {S : Scheme.{u}} (X : AlgebraicSpace S)

/-- Input representable étaleness is the required actual chart property. -/
instance etale : AlgebraicSpace.Etale (map X) where
  of_etale φ hφ := by
    -- Local instance justification (proof-local temporary data): Lift etale composition stability to Over S inside the atlas covering proof, with the component morphisms unchanged.
    letI : (MorphismProperty.over (@AlgebraicGeometry.Etale) :
        MorphismProperty (Over S)).IsStableUnderComposition :=
      { comp_mem := fun {A B C} f g hf hg ↦ by
          -- Local instance justification (proof-local temporary data): Expose the supplied etale certificate hf for the first underlying scheme map in this composition proof.
          letI : AlgebraicGeometry.Etale f.left := hf
          -- Local instance justification (proof-local temporary data): Expose the supplied etale certificate hg for the second underlying scheme map in this composition proof.
          letI : AlgebraicGeometry.Etale g.left := hg
          change AlgebraicGeometry.Etale (f.left ≫ g.left)
          infer_instance }
    exact (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf.comp_mem
      φ (map X) hφ (representableEtale X)

end AlgebraicGeometry.AlgebraicSpace.AtlasInput
