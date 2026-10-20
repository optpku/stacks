module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.H.EtaleCohomology
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ph.AbelianComparison

/-!
# Abelian small-étale to h comparison

The small-to-h inverse image and its canonical inverse-image squares, with comparison-unit
invertibility, positive-degree vanishing, and proper higher-direct-image comparison for
locally torsion coefficients.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open CategoryTheory.GrothendieckTopology
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale.SmallToBig

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.HComparison

variable {X Y : Scheme.{u}}

/-- The composite `smallEtalePullback f ⋙ relocalizationFunctor (𝟙 X)` is continuous from the
small étale topology of `Y` to the big étale topology of `X`. -/
instance isContinuous_smallEtalePullback_comp_relocalization (f : X ⟶ Y) :
    Functor.IsContinuous (smallEtalePullback f ⋙ relocalizationFunctor (𝟙 X))
      Y.smallEtaleTopology (etaleTopology.over X) :=
  Functor.isContinuous_comp (smallEtalePullback f) (relocalizationFunctor (𝟙 X))
    Y.smallEtaleTopology X.smallEtaleTopology (etaleTopology.over X)

/-- The composite `relocalizationFunctor (𝟙 Y) ⋙ Over.pullback f` is continuous from the small
étale topology of `Y` to the big étale topology of `X`. -/
instance isContinuous_relocalization_comp_overPullback (f : X ⟶ Y) :
    Functor.IsContinuous (relocalizationFunctor (𝟙 Y) ⋙ Over.pullback f)
      Y.smallEtaleTopology (etaleTopology.over X) :=
  Functor.isContinuous_comp (relocalizationFunctor (𝟙 Y)) (Over.pullback f)
    Y.smallEtaleTopology (etaleTopology.over Y) (etaleTopology.over X)

/-- Abelian-group-valued sheafification exists on every big h slice at the
topology-comparison coefficient universe. -/
instance hOver_hasSheafify_addCommGrp (X : Scheme.{u}) :
    HasSheafify (hPrecoverage.toGrothendieck.over X) AddCommGrpCat.{u + 1} := sorry

/-- Abelian sheaves on big h slices have injective resolutions at the
topology-comparison coefficient universe. -/
instance hOver_hasInjectiveResolutions (X : Scheme.{u}) :
    HasInjectiveResolutions
      (Sheaf (hPrecoverage.toGrothendieck.over X) AddCommGrpCat.{u + 1}) := sorry

/-- Abelian sheaves on big h slices have Ext groups at the topology-comparison
coefficient universe. -/
instance hOver_hasExt (X : Scheme.{u}) :
    HasExt (Sheaf (hPrecoverage.toGrothendieck.over X) AddCommGrpCat.{u + 1}) := sorry

/-- Abelian sheaves on big étale slices have Ext groups at the topology-comparison
coefficient universe. -/
instance etaleOver_hasExt (X : Scheme.{u}) :
    HasExt (Sheaf (etaleTopology.over X) AddCommGrpCat.{u + 1}) := sorry

/-- Postcomposition on scheme slices admits pointwise right Kan extensions on abelian
presheaves at the topology-comparison coefficient universe. -/
instance overMap_op_hasPointwiseRightKanExtension_addCommGrp (f : X ⟶ Y)
    (P : (Over X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    (Over.map f).op.HasPointwiseRightKanExtension P := sorry

/-- Inverse image `π_X⁻¹` preserves finite limits at the topology-comparison coefficient
universe. -/
instance piInverseImage_preservesFiniteLimits (X : Scheme.{u}) :
    PreservesFiniteLimits (AlgebraicGeometry.Scheme.FppfEtale.piInverseImage X) := sorry

/-- Inverse image `π_X⁻¹` preserves finite colimits at the topology-comparison coefficient
universe. -/
instance piInverseImage_preservesFiniteColimits (X : Scheme.{u}) :
    PreservesFiniteColimits (AlgebraicGeometry.Scheme.FppfEtale.piInverseImage X) := sorry

/-- Inverse image `a_X⁻¹` on abelian sheaves from the small étale site of `X` to the big
h slice `(Sch/X)_h`. -/
def aInverseImage (X : Scheme.{u}) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf (hPrecoverage.toGrothendieck.over X) AddCommGrpCat.{u + 1} :=
  AlgebraicGeometry.Scheme.FppfEtale.piInverseImage X ⋙ comparisonTopologyPullbackAb etale_le_h X

/-- Inverse image `a_X⁻¹` is the composite `π_X⁻¹ ⋙ ε_X⁻¹`. -/
theorem aInverseImage_eq (X : Scheme.{u}) :
    aInverseImage X =
      AlgebraicGeometry.Scheme.FppfEtale.piInverseImage X ⋙ comparisonTopologyPullbackAb etale_le_h X := rfl

/-- The inverse image of a locally torsion small-étale sheaf lies in the comparison
coefficient class `A_X`. -/
theorem aInverseImage_mem_objectProperty {X : Scheme.{u}}
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (hF : F.IsLocallyTorsion) :
    TopologyComparison.objectProperty etale_le_h (fun X ↦ torsionPullback X) X
      ((aInverseImage X).obj F) := sorry

/-- Inverse image `a_X⁻¹` preserves finite limits. -/
instance aInverseImage_preservesFiniteLimits (X : Scheme.{u}) :
    PreservesFiniteLimits (aInverseImage X) :=
  inferInstanceAs
    (PreservesFiniteLimits
      (AlgebraicGeometry.Scheme.FppfEtale.piInverseImage X ⋙ comparisonTopologyPullbackAb etale_le_h X))

/-- Inverse image `a_X⁻¹` preserves finite colimits. -/
instance aInverseImage_preservesFiniteColimits (X : Scheme.{u}) :
    PreservesFiniteColimits (aInverseImage X) :=
  inferInstanceAs
    (PreservesFiniteColimits
      (AlgebraicGeometry.Scheme.FppfEtale.piInverseImage X ⋙ comparisonTopologyPullbackAb etale_le_h X))

/-- Inverse-image square `π_Y⁻¹ ⋙ f_big,étale⁻¹ ≅ f_small⁻¹ ⋙ π_X⁻¹` on abelian sheaves. -/
def abelianSmallEtaleInverseImageSquare (f : X ⟶ Y) :
    AlgebraicGeometry.Scheme.FppfEtale.piInverseImage Y ⋙ etaleTopology.overMapPullback AddCommGrpCat.{u + 1} f ≅
      AlgebraicGeometry.Scheme.PhComparison.smallPullbackAb f ⋙ AlgebraicGeometry.Scheme.FppfEtale.piInverseImage X :=
  let adjBig :=
    etaleTopology.overMapPushforwardAdjunction AddCommGrpCat.{u + 1} f
  let adjπY :=
    (relocalizationFunctor (𝟙 Y)).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
      Y.smallEtaleTopology (etaleTopology.over Y)
  let adjπX :=
    (relocalizationFunctor (𝟙 X)).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
      X.smallEtaleTopology (etaleTopology.over X)
  let adjSmall :=
    (smallEtalePullback f).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
      Y.smallEtaleTopology X.smallEtaleTopology
  let adjBigCont :=
    (Over.pullback f).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
      (etaleTopology.over Y) (etaleTopology.over X)
  let isoPullback :
      etaleTopology.overMapPullback AddCommGrpCat.{u + 1} f ≅
        (Over.pullback f).sheafPullback AddCommGrpCat.{u + 1}
          (etaleTopology.over Y) (etaleTopology.over X) :=
    Adjunction.leftAdjointUniq adjBig adjBigCont
  Functor.isoWhiskerLeft (AlgebraicGeometry.Scheme.FppfEtale.piInverseImage Y) isoPullback ≪≫
    Adjunction.leftAdjointCompIso adjπY adjBigCont (adjSmall.comp adjπX)
      (Functor.sheafPushforwardContinuousComp'
          (AlgebraicGeometry.Scheme.Etale.SmallToBig.fppfSmallRelocalizationSiteIso f).symm AddCommGrpCat.{u + 1}
          Y.smallEtaleTopology (etaleTopology.over Y) (etaleTopology.over X) ≪≫
        (Functor.sheafPushforwardContinuousComp'
          (Iso.refl (smallEtalePullback f ⋙ relocalizationFunctor (𝟙 X)))
          AddCommGrpCat.{u + 1} Y.smallEtaleTopology X.smallEtaleTopology
          (etaleTopology.over X)).symm)

/-- Inverse-image square `a_Y⁻¹ ⋙ f_big,h⁻¹ ≅ f_small⁻¹ ⋙ a_X⁻¹` on abelian sheaves. -/
def abelianSmallHInverseImageSquare (f : X ⟶ Y) :
    aInverseImage Y ⋙
        hPrecoverage.toGrothendieck.overMapPullback AddCommGrpCat.{u + 1} f ≅
      AlgebraicGeometry.Scheme.PhComparison.smallPullbackAb f ⋙ aInverseImage X :=
  (Functor.associator (AlgebraicGeometry.Scheme.FppfEtale.piInverseImage Y) (comparisonTopologyPullbackAb etale_le_h Y)
      (hPrecoverage.toGrothendieck.overMapPullback AddCommGrpCat.{u + 1} f)).symm ≪≫
    Functor.isoWhiskerLeft (AlgebraicGeometry.Scheme.FppfEtale.piInverseImage Y)
      (overMapPullbackComparisonIso etale_le_h f).symm ≪≫
    Functor.associator (AlgebraicGeometry.Scheme.FppfEtale.piInverseImage Y)
      (etaleTopology.overMapPullback AddCommGrpCat.{u + 1} f)
      (comparisonTopologyPullbackAb etale_le_h X) ≪≫
    Functor.isoWhiskerRight (abelianSmallEtaleInverseImageSquare f)
      (comparisonTopologyPullbackAb etale_le_h X) ≪≫
    Functor.associator (AlgebraicGeometry.Scheme.PhComparison.smallPullbackAb f) (AlgebraicGeometry.Scheme.FppfEtale.piInverseImage X)
      (comparisonTopologyPullbackAb etale_le_h X)

/-- For a locally torsion abelian small-étale sheaf, the comparison-adjunction unit
identifies its small-to-big inverse image with the direct image of its small-to-h inverse image. -/
theorem epsilon_pushforward_aInverseImage_unit_isIso {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : F.IsLocallyTorsion) :
    IsIso
      ((comparisonTopologyAdjunction AddCommGrpCat.{u + 1} etale_le_h X).unit.app
        ((AlgebraicGeometry.Scheme.FppfEtale.piInverseImage X).obj F)) := sorry

/-- Positive higher direct images of the small-to-h inverse image of a locally torsion
abelian small-étale sheaf vanish under h-to-étale comparison. -/
theorem epsilon_rightDerived_aInverseImage_isZero {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : F.IsLocallyTorsion) (i : ℕ) (hi : 0 < i) :
    IsZero
      (((comparisonTopologyPushforwardAb etale_le_h X).rightDerived i).obj
        ((aInverseImage X).obj F)) := sorry

/-- Small-to-h inverse image commutes with all higher direct images along a proper
morphism for locally torsion abelian small-étale sheaves. -/
theorem proper_aInverseImage_higherDirectImage {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : F.IsLocallyTorsion) (i : ℕ) :
    IsIsomorphic
      ((aInverseImage Y).obj (((AlgebraicGeometry.Scheme.PhComparison.smallPushforwardAb f).rightDerived i).obj F))
      ((Derived.Over.pushforwardDegree hPrecoverage.toGrothendieck f i).obj
        ((aInverseImage X).obj F)) := sorry

end AlgebraicGeometry.Scheme.HComparison

end

end
