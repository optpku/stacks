/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.Pullback.Module
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.Small.Ringed

/-!
# Restriction from the big fppf site to the small standard sites

This module constructs the ringed-site morphisms and canonical module
base-change map comparing the big fppf site with the small Zariski or étale
site.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.SmallStandardTopology.FppfRestriction

/-- The canonical inclusion of the selected small site into the big fppf
site is a morphism of sites. -/
instance toOver_isMorphismOfSites (σ : SmallStandardTopology) (S : Scheme.{u}) :
    IsMorphismOfSites (σ.topology S) (StandardTopology.fppf.overTopology S)
      (σ.toOver S) := sorry

/-- The canonical inclusion of the selected small site into the big fppf
site is continuous. -/
instance toOver_isContinuous (σ : SmallStandardTopology) (S : Scheme.{u}) :
    (σ.toOver S).IsContinuous (σ.topology S)
      (StandardTopology.fppf.overTopology S) := sorry

/-- The direct-image-form structure map from the selected small structure
sheaf to the restriction of the big fppf structure sheaf. -/
noncomputable def structureMap (σ : SmallStandardTopology) (S : Scheme.{u}) :
    (ringedSite σ S).structureSheaf ⟶
      ((σ.toOver S).sheafPushforwardContinuous RingCat.{u}
        (σ.topology S) (StandardTopology.fppf.overTopology S)).obj
          (StandardTopology.Big.structureSheaf .fppf S) :=
  match σ with
  | .zariski =>
      @Scheme.Site.structureSheafMap _ _ _ _ S.smallZariskiTopology
        (StandardTopology.fppf.overTopology S)
        (Scheme.smallZariskiToScheme S) (Over.forget S)
        (Scheme.smallZariskiForget S)
        (Scheme.SiteRestriction.smallZariskiForget_isContinuous .fppf S) (𝟙 _)
        (Scheme.Zariski.Small.structurePresheaf_isSheaf S)
        (StandardTopology.Big.structurePresheaf_isSheaf .fppf S)
  | .etale =>
      @Scheme.Site.structureSheafMap _ _ _ _ S.smallEtaleTopology
        (StandardTopology.fppf.overTopology S)
        (Scheme.smallEtaleToScheme S) (Over.forget S)
        (MorphismProperty.Over.forget @Etale ⊤ S)
        (Scheme.SiteRestriction.smallEtaleForget_isContinuous .fppf S (by simp)) (𝟙 _)
        (Scheme.Etale.Small.structurePresheaf_isSheaf S)
        (StandardTopology.Big.structurePresheaf_isSheaf .fppf S)

/-- On a small-Zariski object, `structureMap` is induced by the identity of
its underlying scheme. -/
theorem structureMap_zariski_app (S : Scheme.{u})
    (U : S.smallZariskiSiteᵒᵖ) :
    (structureMap .zariski S).hom.app U =
      RingCat.ofHom
        (((𝟙 (Scheme.smallZariskiToScheme S)) :
          Scheme.smallZariskiToScheme S ⟶ Scheme.smallZariskiToScheme S).app
            U.unop).appTop.hom := sorry

/-- On a small-étale object, `structureMap` is induced by the identity of
its underlying scheme. -/
theorem structureMap_etale_app (S : Scheme.{u}) (U : S.Etaleᵒᵖ) :
    (structureMap .etale S).hom.app U =
      RingCat.ofHom
        (((𝟙 (Scheme.smallEtaleToScheme S)) :
          Scheme.smallEtaleToScheme S ⟶ Scheme.smallEtaleToScheme S).app
            U.unop).appTop.hom := sorry

/-- The canonical morphism from the big fppf ringed site to the selected
small Zariski or small étale ringed site. -/
noncomputable def hom (σ : SmallStandardTopology) (S : Scheme.{u}) :
    RingedSite.Hom (StandardTopology.Big.ringedSite .fppf S)
      (ringedSite σ S) where
  base := σ.toOver S
  isMorphismOfSites := toOver_isMorphismOfSites σ S
  structureSheafMap := structureMap σ S

/-- The base functor of `hom` is the canonical forgetful functor to schemes
over the base. -/
theorem hom_base (σ : SmallStandardTopology) (S : Scheme.{u}) :
    (hom σ S).base = σ.toOver S := sorry

/-- The structure-sheaf map of `hom` is the canonical map on global
sections. -/
theorem hom_structureSheafMap (σ : SmallStandardTopology) (S : Scheme.{u}) :
    (hom σ S).structureSheafMap = structureMap σ S := sorry

/-- Restriction of module sheaves from the big fppf site to the selected
small site. -/
noncomputable abbrev restrict (σ : SmallStandardTopology) (S : Scheme.{u}) :
    RingedSite.ModuleCat.{u} (StandardTopology.Big.ringedSite .fppf S) ⥤
      RingedSite.ModuleCat.{u} (ringedSite σ S) :=
  (hom σ S).modulePushforward

/-- `restrict` is the module direct image along the canonical small-to-fppf
site morphism. -/
theorem restrict_def (σ : SmallStandardTopology) (S : Scheme.{u}) :
    restrict σ S = (hom σ S).modulePushforward := sorry

/-- The fppf restriction functor has the canonical module pullback as a left
adjoint. -/
theorem hom_modulePushforward_isRightAdjoint
    (σ : SmallStandardTopology) (S : Scheme.{u}) :
    ((hom σ S).modulePushforward.{u}).IsRightAdjoint := sorry

/-- Pull a big fppf module sheaf to `T` and then restrict it to the selected
small site of `T`. -/
noncomputable abbrev restrictTo (σ : SmallStandardTopology)
    {S T : Scheme.{u}} (g : T ⟶ S)
    (𝒢 : RingedSite.ModuleCat.{u}
      (StandardTopology.Big.ringedSite .fppf S)) :
    RingedSite.ModuleCat.{u} (ringedSite σ T) :=
  (restrict σ T).obj
    ((@RingedSite.Hom.modulePullback _ _
      (StandardTopology.Big.pullbackRingedHom .fppf g)
      (StandardTopology.Big.pullbackRingedHom_modulePushforward_isRightAdjoint
        .fppf g)).obj 𝒢)

/-- `restrictTo` is restriction after canonical big-fppf pullback. -/
theorem restrictTo_def (σ : SmallStandardTopology)
    {S T : Scheme.{u}} (g : T ⟶ S)
    (𝒢 : RingedSite.ModuleCat.{u}
      (StandardTopology.Big.ringedSite .fppf S)) :
    restrictTo σ g 𝒢 =
      (restrict σ T).obj
        ((@RingedSite.Hom.modulePullback _ _
          (StandardTopology.Big.pullbackRingedHom .fppf g)
          (StandardTopology.Big.pullbackRingedHom_modulePushforward_isRightAdjoint
            .fppf g)).obj 𝒢) := sorry

/-- The square formed by big-fppf pullback, small-site pullback, and the two
restriction morphisms commutes. -/
theorem hom_comm (σ : SmallStandardTopology)
    {S T : Scheme.{u}} (g : T ⟶ S) :
    RingedSite.Hom.comp
        (StandardTopology.Big.pullbackRingedHom .fppf g) (hom σ S) =
      RingedSite.Hom.comp (hom σ T) (ringedHom σ g) := sorry

/-- The canonical base-change transformation from small-site pullback after
restriction to restriction after big-fppf pullback. -/
noncomputable def baseChange (σ : SmallStandardTopology)
    {S T : Scheme.{u}} (g : T ⟶ S) :
    restrict σ S ⋙
        (@RingedSite.Hom.modulePullback _ _ (ringedHom σ g)
          (ringedHom_modulePushforward_isRightAdjoint σ g)) ⟶
      (@RingedSite.Hom.modulePullback _ _
        (StandardTopology.Big.pullbackRingedHom .fppf g)
        (StandardTopology.Big.pullbackRingedHom_modulePushforward_isRightAdjoint
          .fppf g)) ⋙ restrict σ T :=
  @RingedSite.Hom.BaseChange.comparisonOfCommSq _ _ _ _
    (StandardTopology.Big.pullbackRingedHom .fppf g)
    (hom σ T) (hom σ S) (ringedHom σ g)
    (StandardTopology.Big.pullbackRingedHom_modulePushforward_isRightAdjoint
      .fppf g)
    (hom_modulePushforward_isRightAdjoint σ T)
    (hom_modulePushforward_isRightAdjoint σ S)
    (ringedHom_modulePushforward_isRightAdjoint σ g)
    (hom_comm σ g)

/-- The component of `baseChange` is the canonical comparison map for the
module sheaf `𝒢`. -/
theorem baseChange_app (σ : SmallStandardTopology)
    {S T : Scheme.{u}} (g : T ⟶ S)
    (𝒢 : RingedSite.ModuleCat.{u}
      (StandardTopology.Big.ringedSite .fppf S)) :
    (baseChange σ g).app 𝒢 =
      (@RingedSite.Hom.BaseChange.comparisonOfCommSq _ _ _ _
        (StandardTopology.Big.pullbackRingedHom .fppf g)
        (hom σ T) (hom σ S) (ringedHom σ g)
        (StandardTopology.Big.pullbackRingedHom_modulePushforward_isRightAdjoint
          .fppf g)
        (hom_modulePushforward_isRightAdjoint σ T)
        (hom_modulePushforward_isRightAdjoint σ S)
        (ringedHom_modulePushforward_isRightAdjoint σ g)
        (hom_comm σ g)).app 𝒢 := sorry

/-- A big-fppf module sheaf is base-change compatible with the selected
small site when every flat, locally finitely presented canonical comparison
component is invertible. -/
def IsBaseChangeCompatible (σ : SmallStandardTopology) {S : Scheme.{u}}
    (𝒢 : RingedSite.ModuleCat.{u}
      (StandardTopology.Big.ringedSite .fppf S)) : Prop :=
  ∀ (T : Scheme.{u}) (g : T ⟶ S) [Flat g] [LocallyOfFinitePresentation g],
    IsIso ((baseChange σ g).app 𝒢)

/-- Base-change compatibility is exactly invertibility of every canonical
comparison component over a flat, locally finitely presented `S`-scheme. -/
theorem isBaseChangeCompatible_iff (σ : SmallStandardTopology) {S : Scheme.{u}}
    (𝒢 : RingedSite.ModuleCat.{u}
      (StandardTopology.Big.ringedSite .fppf S)) :
    IsBaseChangeCompatible σ 𝒢 ↔
      ∀ (T : Scheme.{u}) (g : T ⟶ S) [Flat g]
        [LocallyOfFinitePresentation g], IsIso ((baseChange σ g).app 𝒢) := sorry

end AlgebraicGeometry.SmallStandardTopology.FppfRestriction
