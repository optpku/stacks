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
public import stacks_project.Chap59.Lemma_59_102_4_Comparison

/-!
# Abelian and derived small-étale to big ph comparisons

Abelian inverse image `a_X⁻¹ = π_X⁻¹ ⋙ ε_X⁻¹` on `AddCommGrpCat.{u+1}`, together with the
canonical `D⁺` mate identifying small étale derived direct images with big ph derived
direct images after `a⁻¹`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open CategoryTheory.Adjunction.Derived
open CategoryTheory.ExactFunctor.Derived.Plus (squareIso)
open CategoryTheory.GrothendieckTopology
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale.SmallToBig

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.PhComparison

/-- Slice morphisms in `Over S` admit ordinary pullbacks. -/
instance over_hasPullbacksAlong {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) :
    HasPullbacksAlong f :=
  fun {_} _ => inferInstance

/-- Schemes have ordinary pullbacks along every morphism. -/
instance scheme_hasPullbacksAlong {X Y : Scheme.{u}} (f : X ⟶ Y) :
    HasPullbacksAlong f :=
  fun {_} _ => inferInstance

/-- The identity on an iterated slice is continuous from the étale topology to the ph
topology. -/
instance comparisonOver_etale_le_ph_id_isContinuous {S : Scheme.{u}} (X : Over S) :
    Functor.IsContinuous (𝟭 (Over X))
      ((S.overGrothendieckTopology @Etale).over X) ((Scheme.bigPhSite S).over X) :=
  comparisonOver_id_isContinuous (etale_le_ph S) X

/-- The composite `smallEtalePullback f ⋙ relocalizationFunctor (𝟙 X)` is continuous from the
small étale topology of `Y` to the big étale topology of `X`. -/
instance isContinuous_smallEtalePullback_comp_relocalization
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Functor.IsContinuous (smallEtalePullback f ⋙ relocalizationFunctor (𝟙 X))
      Y.smallEtaleTopology (X.overGrothendieckTopology @Etale) :=
  Functor.isContinuous_comp (smallEtalePullback f) (relocalizationFunctor (𝟙 X))
    Y.smallEtaleTopology X.smallEtaleTopology (X.overGrothendieckTopology @Etale)

/-- The composite `relocalizationFunctor (𝟙 Y) ⋙ Over.pullback f` is continuous from the small
étale topology of `Y` to the big étale topology of `X`. -/
instance isContinuous_relocalization_comp_overPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Functor.IsContinuous (relocalizationFunctor (𝟙 Y) ⋙ Over.pullback f)
      Y.smallEtaleTopology (X.overGrothendieckTopology @Etale) :=
  Functor.isContinuous_comp (relocalizationFunctor (𝟙 Y)) (Over.pullback f)
    Y.smallEtaleTopology (Y.overGrothendieckTopology @Etale)
    (X.overGrothendieckTopology @Etale)

/-- The composite `smallEtalePullback f.left ⋙ piSiteFunctor X` is continuous from the small
étale topology of `Y` to the iterated étale slice of `X`. -/
instance isContinuous_smallEtalePullback_comp_piSiteFunctor
    {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) :
    Functor.IsContinuous (smallEtalePullback f.left ⋙ piSiteFunctor X)
      Y.left.smallEtaleTopology ((S.overGrothendieckTopology @Etale).over X) :=
  Functor.isContinuous_comp (smallEtalePullback f.left) (piSiteFunctor X)
    Y.left.smallEtaleTopology X.left.smallEtaleTopology
    ((S.overGrothendieckTopology @Etale).over X)

/-- The composite `piSiteFunctor Y ⋙ Over.pullback f` is continuous from the small étale
topology of `Y` to the iterated étale slice of `X`. -/
instance isContinuous_piSiteFunctor_comp_overPullback
    {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) :
    Functor.IsContinuous (piSiteFunctor Y ⋙ Over.pullback f)
      Y.left.smallEtaleTopology ((S.overGrothendieckTopology @Etale).over X) :=
  Functor.isContinuous_comp (piSiteFunctor Y) (Over.pullback f)
    Y.left.smallEtaleTopology ((S.overGrothendieckTopology @Etale).over Y)
    ((S.overGrothendieckTopology @Etale).over X)

/-- Abelian-group-valued sheafification exists on every iterated ph slice at the
topology-comparison coefficient universe. -/
instance phSlice_hasSheafify_addCommGrp {S : Scheme.{u}} (X : Over S) :
    HasSheafify ((Scheme.bigPhSite S).over X) AddCommGrpCat.{u + 1} := sorry

/-- Abelian sheaves on iterated ph slices have injective resolutions at the
topology-comparison coefficient universe. -/
instance phSlice_hasInjectiveResolutions {S : Scheme.{u}} (X : Over S) :
    HasInjectiveResolutions
      (Sheaf ((Scheme.bigPhSite S).over X) AddCommGrpCat.{u + 1}) := sorry

/-- Abelian sheaves on iterated ph slices have Ext groups at the topology-comparison
coefficient universe. -/
instance phSlice_hasExt {S : Scheme.{u}} (X : Over S) :
    HasExt (Sheaf ((Scheme.bigPhSite S).over X) AddCommGrpCat.{u + 1}) := sorry

/-- Abelian-group-valued sheafification exists on the small étale site at the
topology-comparison coefficient universe. -/
instance smallEtale_hasSheafify_addCommGrp (X : Scheme.{u}) :
    HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1} := sorry

/-- Abelian sheaves on small étale sites have injective resolutions at the
topology-comparison coefficient universe. -/
instance smallEtale_hasInjectiveResolutions (X : Scheme.{u}) :
    HasInjectiveResolutions
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) := sorry

/-- Abelian sheaves on small étale sites have Ext groups at the topology-comparison
coefficient universe. -/
instance smallEtale_hasExt (X : Scheme.{u}) :
    HasExt (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) := sorry

/-- Abelian sheaves on iterated étale slices have Ext groups at the topology-comparison
coefficient universe. -/
instance etaleSlice_hasExt {S : Scheme.{u}} (X : Over S) :
    HasExt (Sheaf ((S.overGrothendieckTopology @Etale).over X)
      AddCommGrpCat.{u + 1}) := sorry

/-- Small étale base change admits left Kan extensions on abelian presheaves at the
topology-comparison coefficient universe. -/
instance smallEtalePullback_op_hasLeftKanExtension_addCommGrp
    {X Y : Scheme.{u}} (f : X ⟶ Y) (P : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    (smallEtalePullback f).op.HasLeftKanExtension P := sorry

/-- Postcomposition on iterated slices admits pointwise right Kan extensions on abelian
presheaves at the topology-comparison coefficient universe. -/
instance overMap_op_hasPointwiseRightKanExtension_addCommGrp
    {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    (P : (Over X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    (Over.map f).op.HasPointwiseRightKanExtension P := sorry

/-- Inverse image `π_X⁻¹` preserves finite limits. -/
instance piInverseImage_preservesFiniteLimits {S : Scheme.{u}} (X : Over S) :
    PreservesFiniteLimits (piInverseImage X) := sorry

/-- Inverse image `π_X⁻¹` preserves finite colimits. -/
instance piInverseImage_preservesFiniteColimits {S : Scheme.{u}} (X : Over S) :
    PreservesFiniteColimits (piInverseImage X) := sorry

/-- Inverse image `a_X⁻¹ = π_X⁻¹ ⋙ ε_X⁻¹` on abelian sheaves, from the small étale
site of `X` to the iterated ph slice. -/
def aInverseImage {S : Scheme.{u}} (X : Over S) :
    Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf ((Scheme.bigPhSite S).over X) AddCommGrpCat.{u + 1} :=
  piInverseImage X ⋙ comparisonTopologyPullbackAb (etale_le_ph S) X

/-- Inverse image `a_X⁻¹` is the composite `π_X⁻¹ ⋙ ε_X⁻¹`. -/
theorem aInverseImage_eq {S : Scheme.{u}} (X : Over S) :
    aInverseImage X =
      piInverseImage X ⋙ comparisonTopologyPullbackAb (etale_le_ph S) X := sorry

/-- The inverse image of a locally torsion small-étale sheaf lies in the comparison
coefficient class `A_X = ε_{X,*}^{-1}(A'_X)`. -/
theorem aInverseImage_mem_objectProperty {S : Scheme.{u}} {X : Over S}
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : F.IsLocallyTorsion) :
    TopologyComparison.objectProperty (etale_le_ph S) (fun Y ↦ torsionPiInverseImage Y) X
      ((aInverseImage X).obj F) := sorry

/-- Direct image of abelian small-étale sheaves along a morphism of schemes. -/
abbrev smallPushforwardAb {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    Y.smallEtaleTopology X.smallEtaleTopology

/-- `smallPushforwardAb` is sheaf pushforward along `smallEtalePullback`. -/
theorem smallPushforwardAb_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    smallPushforwardAb f =
      (smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        Y.smallEtaleTopology X.smallEtaleTopology := sorry

/-- Inverse image of abelian small-étale sheaves along a morphism of schemes. -/
abbrev smallPullbackAb {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (smallEtalePullback f).sheafPullback AddCommGrpCat.{u + 1}
    Y.smallEtaleTopology X.smallEtaleTopology

/-- `smallPullbackAb` is sheaf pullback along `smallEtalePullback`. -/
theorem smallPullbackAb_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    smallPullbackAb f =
      (smallEtalePullback f).sheafPullback AddCommGrpCat.{u + 1}
        Y.smallEtaleTopology X.smallEtaleTopology := sorry

/-- Inverse image along small étale base change preserves finite limits. -/
instance smallPullbackAb_preservesFiniteLimits {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteLimits (smallPullbackAb f) := sorry

/-- Inverse image along small étale base change preserves finite colimits. -/
instance smallPullbackAb_preservesFiniteColimits {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteColimits (smallPullbackAb f) := sorry

/-- Direct image of abelian small-étale sheaves is additive. -/
instance smallPushforwardAb_additive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (smallPushforwardAb f).Additive := sorry

/-- Inverse image `a_X⁻¹` preserves finite limits. -/
instance aInverseImage_preservesFiniteLimits {S : Scheme.{u}} (X : Over S) :
    PreservesFiniteLimits (aInverseImage X) :=
  inferInstanceAs
    (PreservesFiniteLimits
      (piInverseImage X ⋙ comparisonTopologyPullbackAb (etale_le_ph S) X))

/-- Inverse image `a_X⁻¹` preserves finite colimits. -/
instance aInverseImage_preservesFiniteColimits {S : Scheme.{u}} (X : Over S) :
    PreservesFiniteColimits (aInverseImage X) :=
  inferInstanceAs
    (PreservesFiniteColimits
      (piInverseImage X ⋙ comparisonTopologyPullbackAb (etale_le_ph S) X))

/-- Direct image of abelian sheaves along postcomposition on iterated ph slices. -/
abbrev phPushforwardAb {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) :
    Sheaf ((Scheme.bigPhSite S).over X) AddCommGrpCat.{u + 1} ⥤
      Sheaf ((Scheme.bigPhSite S).over Y) AddCommGrpCat.{u + 1} :=
  (Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
    ((Scheme.bigPhSite S).over X) ((Scheme.bigPhSite S).over Y)

/-- `phPushforwardAb` is the cocontinuous sheaf pushforward along `Over.map`. -/
theorem phPushforwardAb_eq {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) :
    phPushforwardAb f =
      (Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
        ((Scheme.bigPhSite S).over X) ((Scheme.bigPhSite S).over Y) := sorry

/-- Site-level identification of the two paths around the small-étale / big-étale square. -/
def smallEtaleRelocalizationSiteIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
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

/-- Iterated-slice pullback identification `Over.pullback f.left ⋙ X.iteratedSliceBackward ≅
Y.iteratedSliceBackward ⋙ Over.pullback f`. -/
def iteratedSlicePullbackIso {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) :
    Over.pullback f.left ⋙ X.iteratedSliceBackward ≅
      Y.iteratedSliceBackward ⋙ Over.pullback f :=
  conjugateIsoEquiv
    ((Over.iteratedSliceEquiv X).toAdjunction.comp (Over.mapPullbackAdj f.left))
    ((Over.mapPullbackAdj f).comp (Over.iteratedSliceEquiv Y).toAdjunction)
    (Over.iteratedSliceForwardNaturalityIso f).symm

/-- Site-level identification of the two paths around the small-étale / iterated-étale square. -/
def smallEtalePiSiteIso {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) :
    smallEtalePullback f.left ⋙ piSiteFunctor X ≅
      piSiteFunctor Y ⋙ Over.pullback f :=
  (Functor.associator (smallEtalePullback f.left)
      (relocalizationFunctor (𝟙 X.left)) X.iteratedSliceBackward).symm ≪≫
    Functor.isoWhiskerRight (smallEtaleRelocalizationSiteIso f.left)
      X.iteratedSliceBackward ≪≫
    Functor.associator (relocalizationFunctor (𝟙 Y.left))
      (Over.pullback f.left) X.iteratedSliceBackward ≪≫
    Functor.isoWhiskerLeft (relocalizationFunctor (𝟙 Y.left))
      (iteratedSlicePullbackIso f) ≪≫
    (Functor.associator (relocalizationFunctor (𝟙 Y.left))
      Y.iteratedSliceBackward (Over.pullback f)).symm

/-- Inverse-image square `π_Y⁻¹ ⋙ f_big,étale⁻¹ ≅ f_small⁻¹ ⋙ π_X⁻¹` on abelian sheaves. -/
def abelianSmallEtaleInverseImageSquare {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) :
    piInverseImage Y ⋙
        (S.overGrothendieckTopology @Etale).overMapPullback AddCommGrpCat.{u + 1} f ≅
      smallPullbackAb f.left ⋙ piInverseImage X :=
  let adjBig :=
    (S.overGrothendieckTopology @Etale).overMapPushforwardAdjunction
      AddCommGrpCat.{u + 1} f
  let adjπY :=
    (piSiteFunctor Y).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
      Y.left.smallEtaleTopology ((S.overGrothendieckTopology @Etale).over Y)
  let adjπX :=
    (piSiteFunctor X).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
      X.left.smallEtaleTopology ((S.overGrothendieckTopology @Etale).over X)
  let adjSmall :=
    (smallEtalePullback f.left).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
      Y.left.smallEtaleTopology X.left.smallEtaleTopology
  let adjBigCont :=
    (Over.pullback f).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
      ((S.overGrothendieckTopology @Etale).over Y)
      ((S.overGrothendieckTopology @Etale).over X)
  let isoPullback :
      (S.overGrothendieckTopology @Etale).overMapPullback AddCommGrpCat.{u + 1} f ≅
        (Over.pullback f).sheafPullback AddCommGrpCat.{u + 1}
          ((S.overGrothendieckTopology @Etale).over Y)
          ((S.overGrothendieckTopology @Etale).over X) :=
    Adjunction.leftAdjointUniq adjBig adjBigCont
  Functor.isoWhiskerLeft (piInverseImage Y) isoPullback ≪≫
    Adjunction.leftAdjointCompIso adjπY adjBigCont (adjSmall.comp adjπX)
      (Functor.sheafPushforwardContinuousComp'
          (smallEtalePiSiteIso f).symm AddCommGrpCat.{u + 1}
          Y.left.smallEtaleTopology ((S.overGrothendieckTopology @Etale).over Y)
          ((S.overGrothendieckTopology @Etale).over X) ≪≫
        (Functor.sheafPushforwardContinuousComp'
          (Iso.refl (smallEtalePullback f.left ⋙ piSiteFunctor X))
          AddCommGrpCat.{u + 1} Y.left.smallEtaleTopology X.left.smallEtaleTopology
          ((S.overGrothendieckTopology @Etale).over X)).symm)

/-- Inverse-image square `a_Y⁻¹ ⋙ f_big,ph⁻¹ ≅ f_small⁻¹ ⋙ a_X⁻¹` on abelian sheaves. -/
def abelianSmallPhInverseImageSquare {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) :
    aInverseImage Y ⋙
        (Scheme.bigPhSite S).overMapPullback AddCommGrpCat.{u + 1} f ≅
      smallPullbackAb f.left ⋙ aInverseImage X :=
  (Functor.associator (piInverseImage Y) (comparisonTopologyPullbackAb (etale_le_ph S) Y)
      ((Scheme.bigPhSite S).overMapPullback AddCommGrpCat.{u + 1} f)).symm ≪≫
    Functor.isoWhiskerLeft (piInverseImage Y)
      (overMapPullbackComparisonIso (etale_le_ph S) f).symm ≪≫
    Functor.associator (piInverseImage Y)
      ((S.overGrothendieckTopology @Etale).overMapPullback AddCommGrpCat.{u + 1} f)
      (comparisonTopologyPullbackAb (etale_le_ph S) X) ≪≫
    Functor.isoWhiskerRight (abelianSmallEtaleInverseImageSquare f)
      (comparisonTopologyPullbackAb (etale_le_ph S) X) ≪≫
    Functor.associator (smallPullbackAb f.left) (piInverseImage X)
      (comparisonTopologyPullbackAb (etale_le_ph S) X)

/-- Exact inverse image `π_X⁻¹` on abelian small-étale sheaves. -/
abbrev piExact {S : Scheme.{u}} (X : Over S) :
    Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤ₑ
      Sheaf ((S.overGrothendieckTopology @Etale).over X) AddCommGrpCat.{u + 1} :=
  ExactFunctor.of (piInverseImage X)

/-- Exact inverse image along small étale base change. -/
abbrev smallPullbackExact {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤ₑ
      Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  ExactFunctor.of (smallPullbackAb f)

/-- Bundled exact-functor form of the abelian small-étale inverse-image square. -/
def abelianSmallEtaleExactSquare {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) :
    (piExact Y).comp
        ((S.overGrothendieckTopology @Etale).overMapPullbackExact f) ≅
      (smallPullbackExact f.left).comp (piExact X) :=
  (exactFunctor
      (Sheaf Y.left.smallEtaleTopology AddCommGrpCat.{u + 1})
      (Sheaf ((S.overGrothendieckTopology @Etale).over X)
        AddCommGrpCat.{u + 1})).isoMk
    (abelianSmallEtaleInverseImageSquare f)

/-- Bundled exact-functor form of the abelian small-to-ph inverse-image square. -/
def abelianSmallPhExactSquare {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) :
    (ExactFunctor.of (aInverseImage Y)).comp
        ((Scheme.bigPhSite S).overMapPullbackExact f) ≅
      (smallPullbackExact f.left).comp (ExactFunctor.of (aInverseImage X)) :=
  (exactFunctor
      (Sheaf Y.left.smallEtaleTopology AddCommGrpCat.{u + 1})
      (Sheaf ((Scheme.bigPhSite S).over X) AddCommGrpCat.{u + 1})).isoMk
    (abelianSmallPhInverseImageSquare f)

/-- The bounded-below right-derived functor of topology-comparison direct image exists. -/
instance comparisonTopologyPushforwardAb_hasRightDerivedFunctor
    {S : Scheme.{u}} (X : Over S) :
    (comparisonTopologyPushforwardAb (etale_le_ph S) X).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf ((Scheme.bigPhSite S).over X) AddCommGrpCat.{u + 1})) := sorry

/-- The bounded-below right-derived functor of small étale direct image exists. -/
instance smallPushforwardAb_hasRightDerivedFunctor {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (smallPushforwardAb f).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) := sorry

/-- The bounded-below right-derived functor of ph-slice direct image exists. -/
instance phPushforwardAb_hasRightDerivedFunctor
    {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) :
    (phPushforwardAb f).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf ((Scheme.bigPhSite S).over X) AddCommGrpCat.{u + 1})) := sorry

/-- Bounded-below derived inverse image `π_X⁻¹` on `D⁺`. -/
def plusPiInverseImage {S : Scheme.{u}} (X : Over S) :
    DerivedCategory.Plus (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus
        (Sheaf ((S.overGrothendieckTopology @Etale).over X) AddCommGrpCat.{u + 1}) :=
  Plus.left (piExact X)

/-- Bounded-below derived inverse image `a_X⁻¹` on `D⁺`. -/
def plusAInverseImage {S : Scheme.{u}} (X : Over S) :
    DerivedCategory.Plus (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus
        (Sheaf ((Scheme.bigPhSite S).over X) AddCommGrpCat.{u + 1}) :=
  Plus.left (ExactFunctor.of (aInverseImage X))

/-- Derived inverse image `a_X⁻¹` is the exact derived functor of abelian `a_X⁻¹`. -/
theorem plusAInverseImage_eq {S : Scheme.{u}} (X : Over S) :
    plusAInverseImage X = Plus.left (ExactFunctor.of (aInverseImage X)) := sorry

/-- Inverse-image square on `D⁺` induced by the abelian small/étale square. -/
def plusSmallEtaleInverseImageSquare {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) :
    plusPiInverseImage Y ⋙
        Plus.left ((S.overGrothendieckTopology @Etale).overMapPullbackExact f) ≅
      Plus.left (smallPullbackExact f.left) ⋙ plusPiInverseImage X :=
  squareIso
    (piExact Y) ((S.overGrothendieckTopology @Etale).overMapPullbackExact f)
    (smallPullbackExact f.left) (piExact X)
    (abelianSmallEtaleExactSquare f)

/-- Inverse-image square `a_Y⁻¹ ⋙ f_big,ph⁻¹ ≅ f_small⁻¹ ⋙ a_X⁻¹` on `D⁺`. -/
def plusSmallPhInverseImageSquare {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) :
    plusAInverseImage Y ⋙
        Plus.left ((Scheme.bigPhSite S).overMapPullbackExact f) ≅
      Plus.left (smallPullbackExact f.left) ⋙ plusAInverseImage X :=
  squareIso
    (ExactFunctor.of (aInverseImage Y))
    ((Scheme.bigPhSite S).overMapPullbackExact f)
    (smallPullbackExact f.left) (ExactFunctor.of (aInverseImage X))
    (abelianSmallPhExactSquare f)

/-- The morphism `f : X ⟶ Y` of schemes, viewed as an arrow in `Over Y`. -/
def overHomMk {X Y : Scheme.{u}} (f : X ⟶ Y) : Over.mk f ⟶ Over.mk (𝟙 Y) :=
  Over.homMk f

/-- A proper morphism of schemes, viewed in `Over Y`, lies in `properOver Y`. -/
theorem properOver_homMk {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] :
    properOver Y (overHomMk f) := sorry

/-- Canonical `D⁺` mate `a_Y⁻¹ ∘ Rf_small,* ⟶ Rf_big,ph,* ∘ a_X⁻¹`. -/
def plusSmallPhPushforwardHom {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Plus.right (smallPushforwardAb f) ⋙ plusAInverseImage (Over.mk (𝟙 Y)) ⟶
      plusAInverseImage (Over.mk f) ⋙ Plus.right (phPushforwardAb (overHomMk f)) :=
  DerivedBaseChange.map
    (Plus.adjunction (smallPullbackExact f) (smallPushforwardAb f)
      ((smallEtalePullback f).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
        Y.smallEtaleTopology X.smallEtaleTopology))
    (Plus.adjunction
      ((Scheme.bigPhSite Y).overMapPullbackExact (overHomMk f))
      (phPushforwardAb (overHomMk f))
      ((Scheme.bigPhSite Y).overMapCocontinuousAdjunction
        AddCommGrpCat.{u + 1} (overHomMk f)))
    (plusSmallPhInverseImageSquare (overHomMk f))

/-- `plusSmallPhPushforwardHom` is the right mate of the `D⁺` inverse-image square. -/
theorem plusSmallPhPushforwardHom_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    plusSmallPhPushforwardHom f =
      DerivedBaseChange.map
        (Plus.adjunction (smallPullbackExact f) (smallPushforwardAb f)
          ((smallEtalePullback f).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
            Y.smallEtaleTopology X.smallEtaleTopology))
        (Plus.adjunction
          ((Scheme.bigPhSite Y).overMapPullbackExact (overHomMk f))
          (phPushforwardAb (overHomMk f))
          ((Scheme.bigPhSite Y).overMapCocontinuousAdjunction
            AddCommGrpCat.{u + 1} (overHomMk f)))
        (plusSmallPhInverseImageSquare (overHomMk f)) := sorry

end AlgebraicGeometry.Scheme.PhComparison

end

end
