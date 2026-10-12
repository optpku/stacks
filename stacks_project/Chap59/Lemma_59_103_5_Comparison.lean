/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import ReasLib.CategoryTheory.Adjunction.BaseChange
public import ReasLib.CategoryTheory.Adjunction.Derived.Bounded
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Bounded.Square
public import ReasLib.CategoryTheory.Sites.Over.Derived
public import ReasLib.CategoryTheory.Sites.TopologyComparison.Consequences
public import ReasLib.CategoryTheory.Sites.TopologyComparison.HigherDirectImage
public import stacks_project.Chap59.Lemma_59_103_4_Situation
public import stacks_project.Chap59.Lemma_59_103_4_TorsionPullback

/-!
# Abelian and derived small-étale to big h comparisons

Abelian inverse image `a_X⁻¹ = π_X⁻¹ ⋙ ε_X⁻¹` on `AddCommGrpCat.{u+1}`, together with the
canonical `D⁺` mate identifying small étale derived direct images with big h derived
direct images after `a⁻¹`.
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

/-- Schemes have ordinary pullbacks along every morphism. -/
instance scheme_hasPullbacksAlong (f : X ⟶ Y) : HasPullbacksAlong f :=
  fun {_} _ => inferInstance

/-- The identity on `Over X` is continuous from the big étale topology to the big h topology. -/
instance comparisonOver_etale_le_h_id_isContinuous (X : Scheme.{u}) :
    Functor.IsContinuous (𝟭 (Over X)) (etaleTopology.over X)
      (hPrecoverage.toGrothendieck.over X) :=
  comparisonOver_id_isContinuous etale_le_h X

/-- Relocalization from the small étale site of `X` is continuous into the big h slice. -/
instance relocalizationFunctor_isContinuous_h (X : Scheme.{u}) :
    (relocalizationFunctor (𝟙 X)).IsContinuous X.smallEtaleTopology
      (hPrecoverage.toGrothendieck.over X) :=
  Functor.isContinuous_comp' (Functor.rightUnitor (relocalizationFunctor (𝟙 X)))
    X.smallEtaleTopology (etaleTopology.over X)
    (hPrecoverage.toGrothendieck.over X)

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

/-- Abelian sheaves on small étale sites have injective resolutions at the
topology-comparison coefficient universe. -/
instance smallEtale_hasInjectiveResolutions_addCommGrp (X : Scheme.{u}) :
    HasInjectiveResolutions
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) := sorry

/-- Abelian sheaves on small étale sites have Ext groups at the topology-comparison
coefficient universe. -/
instance smallEtale_hasExt_addCommGrp (X : Scheme.{u}) :
    HasExt (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) := sorry

/-- Abelian sheaves on big étale slices have Ext groups at the topology-comparison
coefficient universe. -/
instance etaleOver_hasExt (X : Scheme.{u}) :
    HasExt (Sheaf (etaleTopology.over X) AddCommGrpCat.{u + 1}) := sorry

/-- Small étale base change admits left Kan extensions on abelian presheaves at the
topology-comparison coefficient universe. -/
instance smallEtalePullback_op_hasLeftKanExtension_addCommGrp (f : X ⟶ Y)
    (P : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    (smallEtalePullback f).op.HasLeftKanExtension P := sorry

/-- Postcomposition on scheme slices admits pointwise right Kan extensions on abelian
presheaves at the topology-comparison coefficient universe. -/
instance overMap_op_hasPointwiseRightKanExtension_addCommGrp (f : X ⟶ Y)
    (P : (Over X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    (Over.map f).op.HasPointwiseRightKanExtension P := sorry

/-- Inverse image `π_X⁻¹` preserves finite limits at the topology-comparison coefficient
universe. -/
instance piInverseImage_preservesFiniteLimits (X : Scheme.{u}) :
    PreservesFiniteLimits (piInverseImage X) := sorry

/-- Inverse image `π_X⁻¹` preserves finite colimits at the topology-comparison coefficient
universe. -/
instance piInverseImage_preservesFiniteColimits (X : Scheme.{u}) :
    PreservesFiniteColimits (piInverseImage X) := sorry

/-- Inverse image `a_X⁻¹` on abelian sheaves from the small étale site of `X` to the big
h slice `(Sch/X)_h`. -/
def aInverseImage (X : Scheme.{u}) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf (hPrecoverage.toGrothendieck.over X) AddCommGrpCat.{u + 1} :=
  piInverseImage X ⋙ comparisonTopologyPullbackAb etale_le_h X

/-- Inverse image `a_X⁻¹` is the composite `π_X⁻¹ ⋙ ε_X⁻¹`. -/
theorem aInverseImage_eq (X : Scheme.{u}) :
    aInverseImage X =
      piInverseImage X ⋙ comparisonTopologyPullbackAb etale_le_h X := sorry

/-- The inverse image of a locally torsion small-étale sheaf lies in the comparison
coefficient class `A_X`. -/
theorem aInverseImage_mem_objectProperty {X : Scheme.{u}}
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (hF : F.IsLocallyTorsion) :
    TopologyComparison.objectProperty etale_le_h (fun X ↦ torsionPullback X) X
      ((aInverseImage X).obj F) := sorry

/-- Direct image of abelian small-étale sheaves along a morphism of schemes, at the
topology-comparison coefficient universe. -/
abbrev smallPushforwardAb (f : X ⟶ Y) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    Y.smallEtaleTopology X.smallEtaleTopology

/-- `smallPushforwardAb` is sheaf pushforward along `smallEtalePullback`. -/
theorem smallPushforwardAb_eq (f : X ⟶ Y) :
    smallPushforwardAb f =
      (smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        Y.smallEtaleTopology X.smallEtaleTopology := sorry

/-- Inverse image of abelian small-étale sheaves along a morphism of schemes, at the
topology-comparison coefficient universe. -/
abbrev smallPullbackAb (f : X ⟶ Y) :
    Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (smallEtalePullback f).sheafPullback AddCommGrpCat.{u + 1}
    Y.smallEtaleTopology X.smallEtaleTopology

/-- `smallPullbackAb` is sheaf pullback along `smallEtalePullback`. -/
theorem smallPullbackAb_eq (f : X ⟶ Y) :
    smallPullbackAb f =
      (smallEtalePullback f).sheafPullback AddCommGrpCat.{u + 1}
        Y.smallEtaleTopology X.smallEtaleTopology := sorry

/-- Inverse image along small étale base change preserves finite limits. -/
instance smallPullbackAb_preservesFiniteLimits (f : X ⟶ Y) :
    PreservesFiniteLimits (smallPullbackAb f) := sorry

/-- Inverse image along small étale base change preserves finite colimits. -/
instance smallPullbackAb_preservesFiniteColimits (f : X ⟶ Y) :
    PreservesFiniteColimits (smallPullbackAb f) := sorry

/-- Direct image of abelian small-étale sheaves is additive. -/
instance smallPushforwardAb_additive (f : X ⟶ Y) :
    (smallPushforwardAb f).Additive := sorry

/-- Inverse image `a_X⁻¹` preserves finite limits. -/
instance aInverseImage_preservesFiniteLimits (X : Scheme.{u}) :
    PreservesFiniteLimits (aInverseImage X) :=
  inferInstanceAs
    (PreservesFiniteLimits
      (piInverseImage X ⋙ comparisonTopologyPullbackAb etale_le_h X))

/-- Inverse image `a_X⁻¹` preserves finite colimits. -/
instance aInverseImage_preservesFiniteColimits (X : Scheme.{u}) :
    PreservesFiniteColimits (aInverseImage X) :=
  inferInstanceAs
    (PreservesFiniteColimits
      (piInverseImage X ⋙ comparisonTopologyPullbackAb etale_le_h X))

/-- All-degree local vanishing for the h/étale comparison situation. -/
theorem allVanishing :
    TopologyComparison.Situation.AllVanishing comparisonSituation := sorry

/-- Site-level identification of the two paths around the small-étale / big-étale square. -/
def smallEtaleRelocalizationSiteIso (f : X ⟶ Y) :
    smallEtalePullback f ⋙ relocalizationFunctor (𝟙 X) ≅
      relocalizationFunctor (𝟙 Y) ⋙ Over.pullback f :=
  (Functor.associator (smallEtalePullback f)
      (MorphismProperty.Over.forget (@Etale) ⊤ X) (Over.map (𝟙 X))).symm ≪≫
    Functor.isoWhiskerRight
      (MorphismProperty.Over.pullbackCompForgetIso f :
        smallEtalePullback f ⋙ MorphismProperty.Over.forget (@Etale) ⊤ X ≅
          MorphismProperty.Over.forget (@Etale) ⊤ Y ⋙ Over.pullback f)
      (Over.map (𝟙 X)) ≪≫
    Functor.associator
      (MorphismProperty.Over.forget (@Etale) ⊤ Y) (Over.pullback f) (Over.map (𝟙 X)) ≪≫
    Functor.isoWhiskerLeft (MorphismProperty.Over.forget (@Etale) ⊤ Y)
      (Functor.isoWhiskerLeft (Over.pullback f) (Over.mapId X) ≪≫
        Functor.rightUnitor (Over.pullback f)) ≪≫
    Functor.isoWhiskerLeft (MorphismProperty.Over.forget (@Etale) ⊤ Y)
      ((Functor.leftUnitor (Over.pullback f)).symm ≪≫
        Functor.isoWhiskerRight (Over.mapId Y).symm (Over.pullback f)) ≪≫
    (Functor.associator (MorphismProperty.Over.forget (@Etale) ⊤ Y)
      (Over.map (𝟙 Y)) (Over.pullback f)).symm

/-- Inverse-image square `π_Y⁻¹ ⋙ f_big,étale⁻¹ ≅ f_small⁻¹ ⋙ π_X⁻¹` on abelian sheaves. -/
def abelianSmallEtaleInverseImageSquare (f : X ⟶ Y) :
    piInverseImage Y ⋙ etaleTopology.overMapPullback AddCommGrpCat.{u + 1} f ≅
      smallPullbackAb f ⋙ piInverseImage X :=
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
  Functor.isoWhiskerLeft (piInverseImage Y) isoPullback ≪≫
    Adjunction.leftAdjointCompIso adjπY adjBigCont (adjSmall.comp adjπX)
      (Functor.sheafPushforwardContinuousComp'
          (smallEtaleRelocalizationSiteIso f).symm AddCommGrpCat.{u + 1}
          Y.smallEtaleTopology (etaleTopology.over Y) (etaleTopology.over X) ≪≫
        (Functor.sheafPushforwardContinuousComp'
          (Iso.refl (smallEtalePullback f ⋙ relocalizationFunctor (𝟙 X)))
          AddCommGrpCat.{u + 1} Y.smallEtaleTopology X.smallEtaleTopology
          (etaleTopology.over X)).symm)

/-- Inverse-image square `a_Y⁻¹ ⋙ f_big,h⁻¹ ≅ f_small⁻¹ ⋙ a_X⁻¹` on abelian sheaves. -/
def abelianSmallHInverseImageSquare (f : X ⟶ Y) :
    aInverseImage Y ⋙
        hPrecoverage.toGrothendieck.overMapPullback AddCommGrpCat.{u + 1} f ≅
      smallPullbackAb f ⋙ aInverseImage X :=
  (Functor.associator (piInverseImage Y) (comparisonTopologyPullbackAb etale_le_h Y)
      (hPrecoverage.toGrothendieck.overMapPullback AddCommGrpCat.{u + 1} f)).symm ≪≫
    Functor.isoWhiskerLeft (piInverseImage Y)
      (overMapPullbackComparisonIso etale_le_h f).symm ≪≫
    Functor.associator (piInverseImage Y)
      (etaleTopology.overMapPullback AddCommGrpCat.{u + 1} f)
      (comparisonTopologyPullbackAb etale_le_h X) ≪≫
    Functor.isoWhiskerRight (abelianSmallEtaleInverseImageSquare f)
      (comparisonTopologyPullbackAb etale_le_h X) ≪≫
    Functor.associator (smallPullbackAb f) (piInverseImage X)
      (comparisonTopologyPullbackAb etale_le_h X)

/-- Exact inverse image `π_X⁻¹` on abelian small-étale sheaves. -/
abbrev piExact (X : Scheme.{u}) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤ₑ
      Sheaf (etaleTopology.over X) AddCommGrpCat.{u + 1} :=
  ExactFunctor.of (piInverseImage X)

/-- Exact inverse image along small étale base change. -/
abbrev smallPullbackExact (f : X ⟶ Y) :
    Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤ₑ
      Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  ExactFunctor.of (smallPullbackAb f)

/-- Bundled exact-functor form of the abelian small-étale inverse-image square. -/
def abelianSmallEtaleExactSquare (f : X ⟶ Y) :
    (piExact Y).comp (etaleTopology.overMapPullbackExact f) ≅
      (smallPullbackExact f).comp (piExact X) :=
  (exactFunctor
      (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
      (Sheaf (etaleTopology.over X) AddCommGrpCat.{u + 1})).isoMk
    (abelianSmallEtaleInverseImageSquare f)

/-- Bundled exact-functor form of the abelian small-to-h inverse-image square. -/
def abelianSmallHExactSquare (f : X ⟶ Y) :
    (ExactFunctor.of (aInverseImage Y)).comp
        (hPrecoverage.toGrothendieck.overMapPullbackExact f) ≅
      (smallPullbackExact f).comp (ExactFunctor.of (aInverseImage X)) :=
  (exactFunctor
      (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
      (Sheaf (hPrecoverage.toGrothendieck.over X) AddCommGrpCat.{u + 1})).isoMk
    (abelianSmallHInverseImageSquare f)

/-- The bounded-below right-derived functor of topology-comparison direct image exists. -/
instance comparisonTopologyPushforwardAb_hasRightDerivedFunctor (X : Scheme.{u}) :
    (comparisonTopologyPushforwardAb etale_le_h X).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (hPrecoverage.toGrothendieck.over X) AddCommGrpCat.{u + 1})) := sorry

/-- The bounded-below right-derived functor of small étale direct image exists. -/
instance smallPushforwardAb_hasRightDerivedFunctor (f : X ⟶ Y) :
    (smallPushforwardAb f).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) := sorry

/-- Cocontinuous direct image of abelian sheaves on big h slices. -/
abbrev hPushforwardAb (f : X ⟶ Y) :
    Sheaf (hPrecoverage.toGrothendieck.over X) AddCommGrpCat.{u + 1} ⥤
      Sheaf (hPrecoverage.toGrothendieck.over Y) AddCommGrpCat.{u + 1} :=
  (Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
    (hPrecoverage.toGrothendieck.over X) (hPrecoverage.toGrothendieck.over Y)

/-- `hPushforwardAb` is the cocontinuous sheaf pushforward along `Over.map`. -/
theorem hPushforwardAb_eq (f : X ⟶ Y) :
    hPushforwardAb f =
      (Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
        (hPrecoverage.toGrothendieck.over X)
        (hPrecoverage.toGrothendieck.over Y) := sorry

/-- The bounded-below right-derived functor of big h direct image exists. -/
instance hPushforwardAb_hasRightDerivedFunctor (f : X ⟶ Y) :
    (hPushforwardAb f).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (hPrecoverage.toGrothendieck.over X) AddCommGrpCat.{u + 1})) := sorry

/-- Bounded-below derived inverse image `π_X⁻¹` on `D⁺`. -/
def plusPiInverseImage (X : Scheme.{u}) :
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus (Sheaf (etaleTopology.over X) AddCommGrpCat.{u + 1}) :=
  ExactFunctor.Derived.Plus.functor (piExact X)

/-- Bounded-below derived inverse image `a_X⁻¹` on `D⁺`. -/
def plusAInverseImage (X : Scheme.{u}) :
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus
        (Sheaf (hPrecoverage.toGrothendieck.over X) AddCommGrpCat.{u + 1}) :=
  ExactFunctor.Derived.Plus.functor (ExactFunctor.of (aInverseImage X))

/-- Derived inverse image `a_X⁻¹` is the exact derived functor of abelian `a_X⁻¹`. -/
theorem plusAInverseImage_eq (X : Scheme.{u}) :
    plusAInverseImage X =
      ExactFunctor.Derived.Plus.functor (ExactFunctor.of (aInverseImage X)) := sorry

/-- Inverse-image square on `D⁺` induced by the abelian small/étale square. -/
def plusSmallEtaleInverseImageSquare (f : X ⟶ Y) :
    plusPiInverseImage Y ⋙
        ExactFunctor.Derived.Plus.functor (etaleTopology.overMapPullbackExact f) ≅
      ExactFunctor.Derived.Plus.functor (smallPullbackExact f) ⋙
        plusPiInverseImage X :=
  ExactFunctor.Derived.Plus.squareIso
    (piExact Y) (etaleTopology.overMapPullbackExact f)
    (smallPullbackExact f) (piExact X)
    (abelianSmallEtaleExactSquare f)

/-- Inverse-image square `a_Y⁻¹ ⋙ f_big,h⁻¹ ≅ f_small⁻¹ ⋙ a_X⁻¹` on `D⁺`. -/
def plusSmallHInverseImageSquare (f : X ⟶ Y) :
    plusAInverseImage Y ⋙
        ExactFunctor.Derived.Plus.functor
          (hPrecoverage.toGrothendieck.overMapPullbackExact f) ≅
      ExactFunctor.Derived.Plus.functor (smallPullbackExact f) ⋙
        plusAInverseImage X :=
  ExactFunctor.Derived.Plus.squareIso
    (ExactFunctor.of (aInverseImage Y))
    (hPrecoverage.toGrothendieck.overMapPullbackExact f)
    (smallPullbackExact f) (ExactFunctor.of (aInverseImage X))
    (abelianSmallHExactSquare f)

/-- Canonical `D⁺` mate `a_Y⁻¹ ∘ Rf_small,* ⟶ Rf_big,h,* ∘ a_X⁻¹`. -/
def plusSmallHPushforwardHom (f : X ⟶ Y) :
    Adjunction.Derived.Plus.right (smallPushforwardAb f) ⋙ plusAInverseImage Y ⟶
      plusAInverseImage X ⋙ Adjunction.Derived.Plus.right (hPushforwardAb f) :=
  DerivedBaseChange.map
    (Adjunction.Derived.Plus.adjunction (smallPullbackExact f)
      (smallPushforwardAb f)
      ((smallEtalePullback f).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
        Y.smallEtaleTopology X.smallEtaleTopology))
    (Adjunction.Derived.Plus.adjunction
      (hPrecoverage.toGrothendieck.overMapPullbackExact f)
      (hPushforwardAb f)
      (hPrecoverage.toGrothendieck.overMapCocontinuousAdjunction
        AddCommGrpCat.{u + 1} f))
    (plusSmallHInverseImageSquare f)

/-- `plusSmallHPushforwardHom` is the right mate of the `D⁺` inverse-image square. -/
theorem plusSmallHPushforwardHom_eq (f : X ⟶ Y) :
    plusSmallHPushforwardHom f =
      DerivedBaseChange.map
        (Adjunction.Derived.Plus.adjunction (smallPullbackExact f)
          (smallPushforwardAb f)
          ((smallEtalePullback f).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
            Y.smallEtaleTopology X.smallEtaleTopology))
        (Adjunction.Derived.Plus.adjunction
          (hPrecoverage.toGrothendieck.overMapPullbackExact f)
          (hPushforwardAb f)
          (hPrecoverage.toGrothendieck.overMapCocontinuousAdjunction
            AddCommGrpCat.{u + 1} f))
        (plusSmallHInverseImageSquare f) := sorry

end AlgebraicGeometry.Scheme.HComparison

end

end
