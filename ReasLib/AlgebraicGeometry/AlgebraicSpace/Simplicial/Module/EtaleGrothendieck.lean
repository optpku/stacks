/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SpacesAtlasCharts
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.RingedSite
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Grothendieck
public import Mathlib.CategoryTheory.Sites.InducedTopology
public import Mathlib.CategoryTheory.ShrinkYoneda

/-! # Small charts and module sheaves on a simplicial étale site -/

set_option backward.privateInPublic true
set_option backward.isDefEq.respectTransparency false

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped Simplicial

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial.EtaleModuleDerived

variable {S : Scheme.{u}} (U : SimplicialObject (AlgebraicSpace S))

/-- Morphisms in the total étale site form small types. -/
instance totalLocallySmall : LocallySmall.{u} (SpacesEtale U) where
  hom_small Y Z := by
    apply small_of_injective (f := fun f : Y ⟶ Z ↦
      (f.simplex, Smallness.atlasEvaluation Y.obj.left Z.obj.left f.hom))
    intro f g h
    have hs := congrArg Prod.fst h
    have hh := Smallness.atlasEvaluation_injective _ _ (congrArg Prod.snd h)
    cases f
    cases g
    cases hs
    cases hh
    rfl

/-- The chart indices comprise the affine charts of each simplicial degree. -/
private abbrev ChartIndex :=
  Σ n : SimplexCategoryᵒᵖ, SmallEtale.AtlasCharts.Site (U.obj n)

/-- A chart is interpreted in its own simplicial degree. -/
private def chartObject (i : ChartIndex U) : SpacesEtale U :=
  SpacesEtale.ofStage i.1 ((SpacesEtale.AtlasCharts.inclusion (U.obj i.1)).obj i.2)

/-- The full category on the specified chart objects. -/
private abbrev RawCharts := InducedCategory (SpacesEtale U) (chartObject U)

/-- The chart category has small Hom sets because the total site does. -/
private instance rawChartsLocallySmall : LocallySmall.{u} (RawCharts U) :=
  locallySmall_of_faithful (inducedFunctor (chartObject U))

/-- The same chart objects with small models of their actual Hom sets. -/
private abbrev Charts := ShrinkHoms (RawCharts U)

/-- Inclusion of small charts retains the actual total-site morphisms. -/
private def chartInclusion : Charts U ⥤ SpacesEtale U :=
  (ShrinkHoms.equivalence (RawCharts U)).inverse ⋙ inducedFunctor (chartObject U)

/-- The chart inclusion is full. -/
private instance chartInclusionFull : (chartInclusion U).Full := by
  dsimp [chartInclusion]
  infer_instance

/-- The chart inclusion is faithful. -/
private instance chartInclusionFaithful : (chartInclusion U).Faithful := by
  dsimp [chartInclusion]
  infer_instance

/-- Every total-site object is covered by charts in its own simplicial degree. -/
private theorem chart_is_cover (Y : SpacesEtale U) :
    Sieve.coverByImage (chartInclusion U) Y ∈ spacesEtaleTotalTopology U Y := by
  let G := SpacesEtale.AtlasCharts.inclusion (U.obj Y.index)
  let F := @SpacesEtale.includeStage _ U Y.index
  have h := (CoverPreserving.of_isContinuous F
    (spacesEtaleTopology (U.obj Y.index)) (spacesEtaleTotalTopology U)).cover_preserve
    (G.is_cover_of_isCoverDense (spacesEtaleTopology (U.obj Y.index)) Y.obj)
  apply (spacesEtaleTotalTopology U).superset_covering _ h
  rintro V f ⟨W, g, k, hg, rfl⟩
  rcases hg with ⟨⟨i, b, c, hc⟩⟩
  refine ⟨⟨ShrinkHoms.toShrinkHoms (⟨Y.index, i⟩ : ChartIndex U),
    k ≫ F.map b, F.map c, ?_⟩⟩
  simp only [← Functor.map_comp, Category.assoc, hc]

/-- Every total-site object is covered by the included charts. -/
private instance chartCoverDense :
    (chartInclusion U).IsCoverDense (spacesEtaleTotalTopology U) where
  is_cover := chart_is_cover U

/-- The chart topology is the topology induced from the total étale site. -/
private def chartTopology : GrothendieckTopology (Charts U) :=
  (chartInclusion U).inducedTopology (spacesEtaleTotalTopology U)

/-- The chart family is a dense subsite with its induced topology. -/
private instance chartDense :
    (chartInclusion U).IsDenseSubsite (chartTopology U) (spacesEtaleTotalTopology U) := by
  dsimp [chartTopology]
  infer_instance

/-- Restriction to the dense chart subsite preserves sheaves. -/
private instance chartContinuous :
    (chartInclusion U).IsContinuous (chartTopology U) (spacesEtaleTotalTopology U) := by
  change (chartInclusion U).IsContinuous
    ((chartInclusion U).inducedTopology (spacesEtaleTotalTopology U)) _
  infer_instance

/-- The right Kan indexing categories admit the required additive limits. -/
private instance chartRightKanLimits (V : (SpacesEtale U)ᵒᵖ) :
    HasLimitsOfShape (StructuredArrow V (chartInclusion U).op) AddCommGrpCat.{u} :=
  hasLimitsOfShape_of_essentiallySmall.{u} _ _

/-- Restriction of additive sheaves to the actual small charts. -/
private def chartRestrict :
    Sheaf (spacesEtaleTotalTopology U) AddCommGrpCat.{u} ⥤
      Sheaf (chartTopology U) AddCommGrpCat.{u} :=
  (chartInclusion U).sheafPushforwardContinuous _ _ _

/-- Restriction to a dense subsite is faithful on additive sheaves. -/
private instance chartRestrictFaithful : (chartRestrict U).Faithful := by
  dsimp [chartRestrict]
  infer_instance

/-- Additive sheaves extend from the chart family by right Kan extension. -/
private def chartExtend :
    Sheaf (chartTopology U) AddCommGrpCat.{u} ⥤
      Sheaf (spacesEtaleTotalTopology U) AddCommGrpCat.{u} :=
  (chartInclusion U).sheafPushforwardCocontinuous _ _ _

/-- Restriction and right Kan extension have their canonical adjunction. -/
private def chartAdjunction : chartRestrict U ⊣ chartExtend U :=
  (chartInclusion U).sheafAdjunctionCocontinuous AddCommGrpCat.{u}
    (chartTopology U) (spacesEtaleTotalTopology U)

/-- Abelian sheaves on the total spaces-étale site admit sheafification in the
coefficient universe, computed on the small chart subsite. -/
instance hasSheafifyTotal :
    HasSheafify (etaleTotalRingedSite U).siteTopology AddCommGrpCat.{u} :=
  Functor.IsDenseSubsite.hasSheafify_of_isEquivalence
    (chartTopology U) (spacesEtaleTotalTopology U) (chartInclusion U)

/-- Sheafification equivalences on the total étale site are locally bijective maps. -/
instance locallyBijectiveTotal :
    (etaleTotalRingedSite U).siteTopology.WEqualsLocallyBijective AddCommGrpCat.{u} := sorry

/-- A free module sheaf generated by one of the specified affine charts. -/
private def freeChart (i : ChartIndex U) : RingedSite.ModuleCat.{u} (etaleTotalRingedSite U) :=
  (PresheafOfModules.sheafification (𝟙 (etaleTotalStructureSheaf U).obj)).obj
    ((PresheafOfModules.free (etaleTotalStructureSheaf U).obj).obj
      (shrinkYoneda.{u}.obj (chartObject U i)))

/-- The coproduct of the free module sheaves on the affine charts in every degree. -/
def totalGenerator : RingedSite.ModuleCat.{u} (etaleTotalRingedSite U) :=
  ∐ freeChart U

/-- Free module sheaves on the covering affine charts separate module-sheaf morphisms. -/
theorem totalGenerator_isSeparator : IsSeparator (totalGenerator U) := sorry

/-- Restriction to small charts makes the native module category locally small. -/
instance totalModuleLocallySmall :
    LocallySmall.{u} (RingedSite.ModuleCat.{u} (etaleTotalRingedSite U)) :=
  locallySmall_of_faithful (SheafOfModules.toSheaf (etaleTotalStructureSheaf U) ⋙ chartRestrict U)

/-- Filtered colimits of native module sheaves on the total étale site are exact. -/
instance totalModuleAB5 :
    AB5OfSize.{u, u} (RingedSite.ModuleCat.{u} (etaleTotalRingedSite U)) := sorry

/-- Native module sheaves on the total étale site form a Grothendieck abelian category. -/
instance totalModuleGrothendieck :
    IsGrothendieckAbelian.{u} (RingedSite.ModuleCat.{u} (etaleTotalRingedSite U)) where
  locallySmall := totalModuleLocallySmall U
  ab5OfSize := totalModuleAB5 U
  hasSeparator := ⟨totalGenerator U, totalGenerator_isSeparator U⟩

end AlgebraicGeometry.AlgebraicSpace.Simplicial.EtaleModuleDerived

end
