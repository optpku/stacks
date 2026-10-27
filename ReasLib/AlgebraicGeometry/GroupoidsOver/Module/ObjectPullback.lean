/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.Module
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Localization
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ringed
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Sheafification
public import ReasLib.AlgebraicGeometry.GroupoidsOver.StructureSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Sites.OverPostScheme

/-!
# Objectwise pullback of modules to `(Sch/U)_fppf`

For a category fibred in groupoids `X` over `(Sch/S)_fppf` and an object `x`
lying over `U = p(x)`, restriction to the slice `X_fppf / x` followed by
transport along `overPostScheme` yields the inverse image `x^* F` as a sheaf of
modules on `(Sch/U)_fppf`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- Unfolding of fppf `𝒪_X` as `p.op ⋙ Γ`, then `forget₂`. -/
def structureSheafToPushforward (X : GroupoidsOver S) :
    (structureSheaf X).obj ≅
      (X.p.op ⋙ ((Over.forget S).op ⋙ Scheme.Γ)) ⋙
        forget₂ CommRingCat.{u} RingCat.{u} :=
  (X.p.sheafPushforwardContinuousCompSheafToPresheafIso RingCat.{u}
      (inheritedFppfTopology X) (Scheme.fppfTopology.over S)).app
    (StandardTopology.Big.structureSheaf .fppf S) ≪≫
  (associator X.p.op ((Over.forget S).op ⋙ Scheme.Γ)
      (forget₂ CommRingCat.{u} RingCat.{u})).symm

/-- `structureSheafToPushforward` is the continuous-pushforward identification
reassociated past `forget₂`. -/
theorem structureSheafToPushforward_eq (X : GroupoidsOver S) :
    structureSheafToPushforward X =
      (X.p.sheafPushforwardContinuousCompSheafToPresheafIso RingCat.{u}
          (inheritedFppfTopology X) (Scheme.fppfTopology.over S)).app
        (StandardTopology.Big.structureSheaf .fppf S) ≪≫
      (associator X.p.op ((Over.forget S).op ⋙ Scheme.Γ)
          (forget₂ CommRingCat.{u} RingCat.{u})).symm :=
  sorry

/-- `overPostScheme` is continuous from the localized fppf site of `X` at `x` to
`(Sch/U)_fppf`. -/
instance overPostScheme_isContinuous_fppf (X : GroupoidsOver S) (x : X.total) :
    (overPostScheme X.p x).IsContinuous
      ((ringedSite X).localization x).siteTopology
      (StandardTopology.fppf.overTopology (X.p.obj x).left) :=
  (overPostScheme.isMorphismOfSites X.p x .fppf).toIsContinuous

/-- Reassociation identifying the slice of fppf `𝒪_X` at `x` with the
global-sections presheaf of `Over.forget x ⋙ X.p ⋙ Over.forget S`. -/
def localizationFppfStructurePresheafIso (X : GroupoidsOver S) (x : X.total) :
    ((ringedSite X).localization x).structureSheaf.obj ≅
      Scheme.Site.structurePresheaf (Over.forget x ⋙ X.p ⋙ Over.forget S) :=
  isoWhiskerLeft (Over.forget x).op (structureSheafToPushforward X) ≪≫
    (associator (Over.forget x).op
        (X.p.op ⋙ ((Over.forget S).op ⋙ Scheme.Γ))
        (forget₂ CommRingCat.{u} RingCat.{u})).symm ≪≫
    isoWhiskerRight
      (associator (Over.forget x).op X.p.op
        ((Over.forget S).op ⋙ Scheme.Γ)).symm
      (forget₂ CommRingCat.{u} RingCat.{u}) ≪≫
    isoWhiskerRight
      (associator ((Over.forget x).op ⋙ X.p.op) (Over.forget S).op Scheme.Γ).symm
      (forget₂ CommRingCat.{u} RingCat.{u}) ≪≫
    associator (((Over.forget x).op ⋙ X.p.op) ⋙ (Over.forget S).op) Scheme.Γ
      (forget₂ CommRingCat.{u} RingCat.{u}) ≪≫
    isoWhiskerRight (associator (Over.forget x).op X.p.op (Over.forget S).op)
      (Scheme.Γ ⋙ forget₂ CommRingCat.{u} RingCat.{u}) ≪≫
    isoWhiskerRight
      (isoWhiskerLeft (Over.forget x).op ((X.p).opComp (Over.forget S)).symm)
      (Scheme.Γ ⋙ forget₂ CommRingCat.{u} RingCat.{u}) ≪≫
    isoWhiskerRight ((Over.forget x).opComp (X.p ⋙ Over.forget S)).symm
      (Scheme.Γ ⋙ forget₂ CommRingCat.{u} RingCat.{u})

/-- Objectwise, `localizationFppfStructurePresheafIso` identifies sections of the
slice of fppf `𝒪_X` with global sections of the composite realization. -/
theorem localizationFppfStructurePresheafIso_obj
    (X : GroupoidsOver S) (x : X.total) (y : Over x) :
    ((ringedSite X).localization x).structureSheaf.obj.obj (op y) =
      (Scheme.Site.structurePresheaf
        (Over.forget x ⋙ X.p ⋙ Over.forget S)).obj (op y) :=
  sorry

/-- The comparison `(structureSheaf X).over x ⟶ (overPostScheme X.p x)_* 𝒪_{(Sch/U)_fppf}`
induced by global sections of `overPostSchemeSchemeProjection`, after reassociating the
slice sheaf to that composite's global-sections presheaf. -/
def localizationToBigFppfStructureSheafMap (X : GroupoidsOver S) (x : X.total) :
    ((ringedSite X).localization x).structureSheaf ⟶
      ((overPostScheme X.p x).sheafPushforwardContinuous RingCat.{u}
          ((ringedSite X).localization x).siteTopology
          (StandardTopology.fppf.overTopology (X.p.obj x).left)).obj
        (StandardTopology.Big.structureSheaf .fppf (X.p.obj x).left) :=
  { hom :=
      (localizationFppfStructurePresheafIso X x).hom ≫
        Scheme.Site.structurePresheafMap
          (Over.forget x ⋙ X.p ⋙ Over.forget S)
          (Over.forget (X.p.obj x).left)
          (overPostScheme X.p x)
          (overPostSchemeSchemeProjection X x) }

/-- `localizationToBigFppfStructureSheafMap` is the reassociating iso followed by the
global-sections map of `overPostSchemeSchemeProjection`. -/
theorem localizationToBigFppfStructureSheafMap_hom
    (X : GroupoidsOver S) (x : X.total) :
    (localizationToBigFppfStructureSheafMap X x).hom =
      (localizationFppfStructurePresheafIso X x).hom ≫
        Scheme.Site.structurePresheafMap
          (Over.forget x ⋙ X.p ⋙ Over.forget S)
          (Over.forget (X.p.obj x).left)
          (overPostScheme X.p x)
          (overPostSchemeSchemeProjection X x) :=
  sorry

/-- The morphism of ringed sites from the localized fppf site of `X` at `x` to the big
fppf site of `U = p(x)`, with base functor `overPostScheme X.p x`. -/
def localizationToBigFppf (X : GroupoidsOver S) (x : X.total) :
    RingedSite.Hom
      (StandardTopology.Big.ringedSite .fppf (X.p.obj x).left)
      ((ringedSite X).localization x) where
  base := overPostScheme X.p x
  isMorphismOfSites := overPostScheme.isMorphismOfSites X.p x .fppf
  structureSheafMap := localizationToBigFppfStructureSheafMap X x

/-- The base functor of `localizationToBigFppf` is `overPostScheme` of the projection. -/
theorem localizationToBigFppf_base (X : GroupoidsOver S) (x : X.total) :
    (localizationToBigFppf X x).base = overPostScheme X.p x :=
  sorry

/-- The structure-sheaf map of `localizationToBigFppf` is
`localizationToBigFppfStructureSheafMap`. -/
theorem localizationToBigFppf_structureSheafMap (X : GroupoidsOver S) (x : X.total) :
    (localizationToBigFppf X x).structureSheafMap =
      localizationToBigFppfStructureSheafMap X x :=
  sorry

/-- The functor from the localized fppf site to the big fppf site of the underlying
scheme is a dense subsite functor. -/
private instance localizationFppf_forwardDense (X : GroupoidsOver S) (x : X.total) :
    (LocalizationGeometry.siteEquivalence X x).functor.IsDenseSubsite
      ((ringedSite X).localization x).siteTopology
      (StandardTopology.fppf.overTopology (X.p.obj x).left) :=
  overPostScheme.isDenseSubsite X.p x .fppf

/-- The inverse equivalence from the big fppf site of the underlying scheme to the
localized fppf site is a dense subsite functor. -/
private instance localizationFppf_backwardDense (X : GroupoidsOver S) (x : X.total) :
    (LocalizationGeometry.siteEquivalence X x).inverse.IsDenseSubsite
      (StandardTopology.fppf.overTopology (X.p.obj x).left)
      ((ringedSite X).localization x).siteTopology := by
  change (LocalizationGeometry.siteEquivalence X x).symm.functor.IsDenseSubsite _ _
  have topology_eq := @Equivalence.eq_inducedTopology_of_isDenseSubsite _ _
    (StandardTopology.fppf.overTopology (X.p.obj x).left) _ _
    ((ringedSite X).localization x).siteTopology
    (LocalizationGeometry.siteEquivalence X x).symm (localizationFppf_forwardDense X x)
  rw [topology_eq]
  infer_instance

/-- Module pushforward from the big fppf site to the localized site has a left adjoint
constructed by inverse transport of modules and their coefficient rings. -/
instance localizationToBigFppf_modulePushforward_isRightAdjoint
    (X : GroupoidsOver S) (x : X.total) :
    ((localizationToBigFppf X x).modulePushforward.{u}).IsRightAdjoint := by
  let coefficientPresheafIso :
      ((ringedSite X).localization x).structureSheaf.obj ≅
        (overPostScheme X.p x).op ⋙
          (StandardTopology.Big.structureSheaf .fppf (X.p.obj x).left).obj :=
    localizationFppfStructurePresheafIso X x ≪≫
      isoWhiskerRight (NatIso.op (LocalizationGeometry.projectionIso X x)).symm
        (Scheme.Γ ⋙ forget₂ CommRingCat RingCat)
  let coefficientIso :
      ((ringedSite X).localization x).structureSheaf ≅
        ((LocalizationGeometry.siteEquivalence X x).functor.sheafPushforwardContinuous
          RingCat.{u} ((ringedSite X).localization x).siteTopology
          (StandardTopology.fppf.overTopology (X.p.obj x).left)).obj
          (StandardTopology.Big.structureSheaf .fppf (X.p.obj x).left) :=
    (fullyFaithfulSheafToPresheaf _ _).preimageIso coefficientPresheafIso
  have coefficientIso_hom : coefficientIso.hom =
      localizationToBigFppfStructureSheafMap X x := by
    apply (fullyFaithfulSheafToPresheaf _ _).map_injective
    apply NatTrans.ext
    funext U
    rfl
  have adjunction := SheafOfModules.CoefficientEquivalence.adjunction
    (LocalizationGeometry.siteEquivalence X x) coefficientIso
  rw [coefficientIso_hom] at adjunction
  exact adjunction.isRightAdjoint

/-- The big fppf ringed site `(Sch/U)_fppf` of the scheme `U = p(x)`. -/
abbrev objectPullbackSite (X : GroupoidsOver S) (x : X.total) :=
  StandardTopology.Big.ringedSite .fppf (X.p.obj x).left

/-- `objectPullbackSite X x` is the big fppf ringed site of `p(x)`. -/
theorem objectPullbackSite_eq (X : GroupoidsOver S) (x : X.total) :
    objectPullbackSite X x =
      StandardTopology.Big.ringedSite .fppf (X.p.obj x).left :=
  sorry

/-- Inverse image `x^* F` of an `𝒪_X`-module along an object `x` of `X`, as a sheaf of
modules on `(Sch/U)_fppf` with `U = p(x)`. This is restriction to `X_fppf / x` followed
by transport along `localizationToBigFppf`. -/
def objectPullback (X : GroupoidsOver S) (x : X.total) :
    SheafOfModules.{u} (structureSheaf X) ⥤
      RingedSite.ModuleCat.{u} (objectPullbackSite X x) :=
  RingedSite.Hom.localizedRestriction (ringedSite X) x ⋙
    (localizationToBigFppf X x).modulePullback.{u}

/-- `objectPullback X x` is slice restriction followed by inverse image along
`localizationToBigFppf`. -/
theorem objectPullback_eq (X : GroupoidsOver S) (x : X.total) :
    objectPullback X x =
      RingedSite.Hom.localizedRestriction (ringedSite X) x ⋙
        (localizationToBigFppf X x).modulePullback.{u} :=
  sorry

/-- Weak sheafification exists on every slice of `(Sch/U)_fppf` for `U = p(x)`. -/
instance objectPullback_hasWeakSheafify (X : GroupoidsOver S) (x : X.total) :
    ∀ U : (objectPullbackSite X x).carrier,
      HasWeakSheafify ((objectPullbackSite X x).siteTopology.over U)
        AddCommGrpCat.{u} :=
  StandardTopology.Big.over_hasWeakSheafify .fppf (X.p.obj x).left

/-- Sheafification equivalences on slices of `(Sch/U)_fppf` are the locally
bijective morphisms. -/
instance objectPullback_wEqualsLocallyBijective
    (X : GroupoidsOver S) (x : X.total) :
    ∀ U : (objectPullbackSite X x).carrier,
      ((objectPullbackSite X x).siteTopology.over U).WEqualsLocallyBijective
        AddCommGrpCat.{u} :=
  StandardTopology.Big.over_wEqualsLocallyBijective .fppf (X.p.obj x).left

/-- Ring-to-abelian-group sheaf composition exists on every slice of
`(Sch/U)_fppf` for `U = p(x)`. -/
instance objectPullback_hasSheafCompose (X : GroupoidsOver S) (x : X.total) :
    ∀ U : (objectPullbackSite X x).carrier,
      ((objectPullbackSite X x).siteTopology.over U).HasSheafCompose
        (forget₂ RingCat.{u} AddCommGrpCat.{u}) :=
  StandardTopology.Big.over_hasSheafCompose_ring_addCommGrp .fppf (X.p.obj x).left

end AlgebraicGeometry.GroupoidsOver
