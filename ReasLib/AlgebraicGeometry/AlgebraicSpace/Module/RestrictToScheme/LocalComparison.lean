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

/-- Regard a chart over `U` as an object of the slice of the ambient étale site. -/
def chartToSlice {X : AlgebraicSpace S} (U : smallEtaleSite X) :
    smallEtaleSite (ofOver U.left) ⥤ Over U where
  obj V := Over.mk (MorphismProperty.CostructuredArrow.homMk
    (B := U) (yonedaEquiv V.hom) trivial sorry :
      (Modules.restrictPostcompose U.hom).obj V ⟶ U)
  map f := Over.homMk (MorphismProperty.CostructuredArrow.homMk f.left trivial sorry) sorry
  map_id := sorry
  map_comp := sorry

/-- Recover a chart over `U` from an arrow in the slice site. -/
def sliceToChart {X : AlgebraicSpace S} (U : smallEtaleSite X) :
    Over U ⥤ smallEtaleSite (ofOver U.left) where
  obj V := smallEtaleSite.mk (ofOverMap V.hom.left)
    (SmallEtaleGlueing.etale_siteHom V.hom)
  map f := MorphismProperty.CostructuredArrow.homMk f.left.left trivial sorry
  map_id := sorry
  map_comp := sorry

/-- Chart reconstruction is the identity on the underlying represented schemes. -/
def chartSliceUnitIso {X : AlgebraicSpace S} (U : smallEtaleSite X) :
    𝟭 (smallEtaleSite (ofOver U.left)) ≅ chartToSlice U ⋙ sliceToChart U :=
  NatIso.ofComponents (fun V ↦
    { hom := MorphismProperty.CostructuredArrow.homMk (𝟙 V.left) trivial sorry
      inv := MorphismProperty.CostructuredArrow.homMk (𝟙 V.left) trivial sorry
      hom_inv_id := sorry
      inv_hom_id := sorry }) sorry

/-- Slice reconstruction is the identity on the underlying represented schemes. -/
def chartSliceCounitIso {X : AlgebraicSpace S} (U : smallEtaleSite X) :
    sliceToChart U ⋙ chartToSlice U ≅ 𝟭 (Over U) :=
  NatIso.ofComponents (fun V ↦
    { hom := Over.homMk (MorphismProperty.CostructuredArrow.homMk
          (𝟙 V.left.left) trivial sorry) sorry
      inv := Over.homMk (MorphismProperty.CostructuredArrow.homMk
          (𝟙 V.left.left) trivial sorry) sorry
      hom_inv_id := sorry
      inv_hom_id := sorry }) sorry

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

/-- Both structure sheaves evaluate at the same represented scheme in the slice. -/
def sliceStructureIso {X : AlgebraicSpace S} (U : smallEtaleSite X) :
    structureSheaf (ofOver U.left) ≅
      ((chartToSlice U).sheafPushforwardContinuous RingCat.{u}
        (smallEtaleTopology (ofOver U.left)) ((smallEtaleTopology X).over U)).obj
          ((structureSheaf X).over U) where
  hom := ⟨{ app := fun _ ↦ 𝟙 _, naturality := sorry }⟩
  inv := ⟨{ app := fun _ ↦ 𝟙 _, naturality := sorry }⟩
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Convert a module on the slice site into a module on the represented chart. -/
def sliceModules {X : AlgebraicSpace S} (U : smallEtaleSite X) :
    SheafOfModules.{u} ((structureSheaf X).over U) ⥤ (ofOver U.left).Modules :=
  SheafOfModules.pushforward (sliceStructureIso U).hom

/-- The displayed site and ring equivalences make slice conversion a left adjoint. -/
instance sliceModules_isLeftAdjoint {X : AlgebraicSpace S} (U : smallEtaleSite X) :
    (sliceModules U).IsLeftAdjoint :=
  SheafOfModules.isLeftAdjoint_pushforward_of_isIso (sliceStructureIso U).hom

/-- The structure module is unchanged by converting the slice presentation. -/
def sliceModulesUnitIso {X : AlgebraicSpace S} (U : smallEtaleSite X) :
    SheafOfModules.unit (structureSheaf (ofOver U.left)) ≅
      (sliceModules U).obj (SheafOfModules.unit ((structureSheaf X).over U)) :=
  Iso.refl _

/-- Restricting to the slice and converting it to the chart preserves every section. -/
def sliceRestrictionIso {X : AlgebraicSpace S} (U : smallEtaleSite X) :
    SheafOfModules.overFunctor (structureSheaf X) U ⋙ sliceModules U ≅
      @Modules.restrictFunctor S (ofOver U.left) X U.hom U.prop :=
  NatIso.ofComponents (fun M ↦
    { hom := { val := { app := fun _ ↦ 𝟙 _, naturality := sorry } }
      inv := { val := { app := fun _ ↦ 𝟙 _, naturality := sorry } }
      hom_inv_id := sorry
      inv_hom_id := sorry }) sorry

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
