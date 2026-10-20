/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ph.EtaleComparison
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.InverseImage.Exact
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SmallToBig.FppfPushforward
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Additive
public import ReasLib.CategoryTheory.Sites.Over.Derived
public import ReasLib.CategoryTheory.Sites.TopologyComparison.HigherDirectImage

/-!
# Abelian small-étale to ph comparison

The composite small-to-ph inverse image and its inverse-image squares, together with
comparison-unit invertibility, higher-direct-image vanishing, and proper direct-image
comparison for locally torsion abelian sheaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
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
      piInverseImage X ⋙ comparisonTopologyPullbackAb (etale_le_ph S) X := rfl

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
        Y.smallEtaleTopology X.smallEtaleTopology := rfl

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
        Y.smallEtaleTopology X.smallEtaleTopology := rfl

/-- Inverse image along small étale base change preserves finite colimits. -/
instance smallPullbackAb_preservesFiniteColimits {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteColimits (smallPullbackAb f) :=
  ((exactFunctor_iff (smallPullbackAb f)).mp
    (smallEtaleInverseImage_exact_addCommGrp.{u, u + 1} f)).2

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
        ((Scheme.bigPhSite S).over X) ((Scheme.bigPhSite S).over Y) := rfl

/-- Site-level identification of the two paths around the small-étale / iterated-étale square. -/
def smallEtalePiSiteIso {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) :
    smallEtalePullback f.left ⋙ piSiteFunctor X ≅
      piSiteFunctor Y ⋙ Over.pullback f :=
  (Functor.associator (smallEtalePullback f.left)
      (relocalizationFunctor (𝟙 X.left)) X.iteratedSliceBackward).symm ≪≫
    Functor.isoWhiskerRight (AlgebraicGeometry.Scheme.Etale.SmallToBig.fppfSmallRelocalizationSiteIso f.left)
      X.iteratedSliceBackward ≪≫
    Functor.associator (relocalizationFunctor (𝟙 Y.left))
      (Over.pullback f.left) X.iteratedSliceBackward ≪≫
    Functor.isoWhiskerLeft (relocalizationFunctor (𝟙 Y.left))
      (conjugateIsoEquiv
        ((Over.iteratedSliceEquiv X).toAdjunction.comp (Over.mapPullbackAdj f.left))
        ((Over.mapPullbackAdj f).comp (Over.iteratedSliceEquiv Y).toAdjunction)
        (Over.iteratedSliceForwardNaturalityIso f).symm) ≪≫
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

/-- The topology-comparison unit at the inverse image of a locally torsion small-étale
sheaf is an isomorphism. -/
theorem epsilon_pushforward_aInverseImage_unit_isIso {S : Scheme.{u}} {X : Over S}
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : F.IsLocallyTorsion) :
    IsIso
      ((comparisonTopologyAdjunction AddCommGrpCat.{u + 1} (etale_le_ph S) X).unit.app
        ((piInverseImage X).obj F)) := sorry

/-- Positive-degree topology-comparison direct images of the small-to-ph inverse image
of a locally torsion small-étale sheaf vanish. -/
theorem epsilon_rightDerived_aInverseImage_isZero {S : Scheme.{u}} {X : Over S}
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : F.IsLocallyTorsion) (i : ℕ) (hi : 0 < i) :
    IsZero
      (((comparisonTopologyPushforwardAb (etale_le_ph S) X).rightDerived i).obj
        ((aInverseImage X).obj F)) := sorry

/-- Small-to-ph inverse image commutes, up to isomorphism, with every higher direct image
along a proper morphism in a scheme slice. -/
theorem proper_aInverseImage_higherDirectImage {S : Scheme.{u}} {X Y : Over S}
    (f : X ⟶ Y) (hf : properOver S f)
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : F.IsLocallyTorsion) (i : ℕ) :
    IsIsomorphic
      ((aInverseImage Y).obj (((smallPushforwardAb f.left).rightDerived i).obj F))
      ((Derived.Over.pushforwardDegree (Scheme.bigPhSite S) f i).obj
        ((aInverseImage X).obj F)) := sorry

end AlgebraicGeometry.Scheme.PhComparison

end

end
