/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pushforward.Composition
public import ReasLib.CategoryTheory.Sites.Topos.ModuleAdjunction
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap94.«94_8_2_1_FullyFaithful»
public import stacks_project.Chap96.Lemma_96_13_2
public import stacks_project.Chap96.Lemma_96_14_2_Restriction
public import ReasLib.CategoryTheory.Fibered.InheritedTopology.Morphism
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Pseudofunctor
public import ReasLib.CategoryTheory.Fibered.Groupoids.UnderlyingFunctorIso
public import stacks_project.Chap96.«96_10_3_1_Comparison»

/-!
# Pullback compatibility of quasi-coherent restriction

Restriction `ℱ ↦ ℱ|_{F_étale}` intertwines pullback along a 1-morphism of
categories fibred in groupoids with small-étale pullback along the recovered
morphism of representing algebraic spaces.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor
open CategoryTheory.ObjectProperty CategoryTheory.Sheaf.InternalModule
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- The morphism of algebraic spaces recovered from a 1-morphism of categories
fibred in groupoids along representing equivalences. This is `inducedHom` of
Lemma 96.10.3, obtained from `toGroupoids.recover` without importing the
ringed-topos square of 96.10.3 (which cannot be imported with `QCoh.pullback`). -/
abbrev recoveredHom {F G : AlgebraicSpace S} {X Y : GroupoidsOver S}
    (eX : F.toGroupoids ≌ X) (eY : G.toGroupoids ≌ Y) (f : X ⟶ Y) : F ⟶ G :=
  AlgebraicSpace.toGroupoids.recover eX.symm eY.symm f

/-- `recoveredHom eX eY f` is recovery of `f` along `eX.symm` and `eY.symm`. -/
theorem recoveredHom_eq {F G : AlgebraicSpace S} {X Y : GroupoidsOver S}
    (eX : F.toGroupoids ≌ X) (eY : G.toGroupoids ≌ Y) (f : X ⟶ Y) :
    recoveredHom eX eY f = AlgebraicSpace.toGroupoids.recover eX.symm eY.symm f :=
  rfl

/-- The cartesian total functor agrees with `toFunctor`. -/
theorem cartesian_toFunctor_eq {X Y : GroupoidsOver S} (h : X ⟶ Y) :
    (toCartesianBasedFunctor h).toFunctor = toFunctor h :=
  congrArg (fun F => F.toFunctor) (toCartesianBasedFunctor.toBasedFunctor h)

/-- Associated étale topologies admit type-valued sheafification in universe `u`. -/
instance etaleTopology_hasSheafify_type (X : GroupoidsOver S) :
    HasSheafify X.etaleTopology (Type u) :=
  sorry

/-- Associated étale topologies admit weak type-valued sheafification in universe `u`. -/
instance etaleTopology_hasWeakSheafify_type (X : GroupoidsOver S) :
    HasWeakSheafify X.etaleTopology (Type u) :=
  sorry

/-- Pointwise right Kan extensions exist for type-valued presheaves along a cartesian
total functor. -/
instance toCartesian_op_hasPointwiseRightKanExtension_type {X Y : GroupoidsOver S}
    (h : X ⟶ Y) (P : X.totalᵒᵖ ⥤ Type u) :
    (toCartesianBasedFunctor h).toFunctor.op.HasPointwiseRightKanExtension P :=
  sorry

/-- The total functor of a 1-morphism is a morphism of associated étale sites. -/
instance toFunctor_isMorphismOfSites_etale {X Y : GroupoidsOver S} (h : X ⟶ Y) :
    IsMorphismOfSites X.etaleTopology Y.etaleTopology (toFunctor h) :=
  sorry

/-- The total functor of a 1-morphism is continuous for associated étale topologies. -/
instance toFunctor_isContinuous_etale {X Y : GroupoidsOver S} (h : X ⟶ Y) :
    (toFunctor h).IsContinuous X.etaleTopology Y.etaleTopology :=
  (toFunctor_isMorphismOfSites_etale h).toIsContinuous

/-- Restriction of scalars along the inverse-image structure map of
`toGroupoidsEtaleRingedToposHom` is a right adjoint. -/
instance toGroupoidsEtaleRingedToposHom_restrictScalars_isRightAdjoint
    {F G : AlgebraicSpace S} (h : F ⟶ G) :
    (SheafOfModules.restrictScalars.{u}
      (AlgebraicSpace.toGroupoidsEtaleRingedToposHom h).structureMap).IsRightAdjoint :=
  sorry

/-- Realization projection `toFunctor h ⋙ Y.p ⋙ forget ⟶ X.p ⋙ forget` from the
commuting triangle of a 1-morphism of categories fibred in groupoids. -/
def toFunctor_realization_projection {X Y : GroupoidsOver S} (h : X ⟶ Y) :
    toFunctor h ⋙ Y.p ⋙ Over.forget S ⟶ X.p ⋙ Over.forget S :=
  eqToHom
    (congrArg (fun F => F ⋙ Over.forget S)
      ((congrArg (fun F => F ⋙ Y.p) (cartesian_toFunctor_eq h).symm).trans
        (toCartesianBasedFunctor h).toBasedFunctor.w))

/-- Structure-sheaf map of the étale ringed-site morphism attached to a
1-morphism, as the global-sections pullback conjugated by
`structureSheafPresentationIso`. -/
def etaleSiteHom_structureSheafMap {X Y : GroupoidsOver S} (h : X ⟶ Y) :
    (etaleRingedSite X).structureSheaf ⟶
      ((toFunctor h).sheafPushforwardContinuous RingCat.{u}
        X.etaleTopology Y.etaleTopology).obj (etaleRingedSite Y).structureSheaf :=
  (structureSheafPresentationIso X).hom ≫
    Scheme.Site.structureSheafMap
      X.etaleTopology Y.etaleTopology
      (X.p ⋙ Over.forget S) (Y.p ⋙ Over.forget S)
      (toFunctor h) (toFunctor_realization_projection h)
      (etaleRingedSite_structurePresheaf_isSheaf X)
      (etaleRingedSite_structurePresheaf_isSheaf Y) ≫
      ((toFunctor h).sheafPushforwardContinuous RingCat.{u}
          X.etaleTopology Y.etaleTopology).map
        (structureSheafPresentationIso Y).inv

/-- The morphism of étale ringed sites induced by a 1-morphism of categories
fibred in groupoids, with underlying functor `toFunctor h`. -/
def etaleSiteHom {X Y : GroupoidsOver S} (h : X ⟶ Y) :
    RingedSite.Hom (etaleRingedSite Y) (etaleRingedSite X) where
  base := toFunctor h
  isMorphismOfSites := toFunctor_isMorphismOfSites_etale h
  structureSheafMap := etaleSiteHom_structureSheafMap h

/-- Inverse image `h^*` of étale `𝒪`-modules along a 1-morphism. -/
def etaleModuleInverseImage {X Y : GroupoidsOver S} (h : X ⟶ Y) :
    SheafOfModules.{u} (etaleRingedSite Y).structureSheaf ⥤
      SheafOfModules.{u} (etaleRingedSite X).structureSheaf :=
  (etaleSiteHom h).modulePushforward.{u}

/-- Continuity of the base of `etaleSiteHom` on the étale ringed sites. -/
instance etaleSiteHom_base_isContinuous {X Y : GroupoidsOver S} (h : X ⟶ Y) :
    (etaleSiteHom h).base.IsContinuous
      (etaleRingedSite X).siteTopology (etaleRingedSite Y).siteTopology :=
  (etaleSiteHom h).isMorphismOfSites.toIsContinuous

/-- Continuity of a composite of `etaleSiteHom` bases. -/
instance etaleSiteHom_baseComp_isContinuous {X Y Z : GroupoidsOver S}
    (h : X ⟶ Y) (k : Y ⟶ Z) :
    ((etaleSiteHom h).base ⋙ (etaleSiteHom k).base).IsContinuous
      (etaleRingedSite X).siteTopology (etaleRingedSite Z).siteTopology :=
  Functor.isContinuous_comp (etaleSiteHom h).base (etaleSiteHom k).base
    (etaleRingedSite X).siteTopology (etaleRingedSite Y).siteTopology
    (etaleRingedSite Z).siteTopology

/-- A composite of total functors is continuous for associated étale topologies. -/
instance toFunctor_comp_isContinuous_etale {X Y Z : GroupoidsOver S}
    (h : X ⟶ Y) (k : Y ⟶ Z) :
    (toFunctor h ⋙ toFunctor k).IsContinuous X.etaleTopology Z.etaleTopology :=
  Functor.isContinuous_comp (toFunctor h) (toFunctor k)
    X.etaleTopology Y.etaleTopology Z.etaleTopology

/-- The composite structure-sheaf map along `toFunctor h ⋙ toFunctor k`. -/
def etaleSiteHom_structureSheafMap_compData {X Y Z : GroupoidsOver S}
    (h : X ⟶ Y) (k : Y ⟶ Z) :
    (etaleRingedSite X).structureSheaf ⟶
      ((toFunctor h ⋙ toFunctor k).sheafPushforwardContinuous RingCat.{u}
        X.etaleTopology Z.etaleTopology).obj (etaleRingedSite Z).structureSheaf :=
  (etaleSiteHom h).structureSheafMap ≫
    ((toFunctor h).sheafPushforwardContinuous RingCat.{u}
        X.etaleTopology Y.etaleTopology).map (etaleSiteHom k).structureSheafMap

/-- Module inverse image along a composite, before transporting the total functor. -/
def etaleModuleInverseImage_comp₀ {X Y Z : GroupoidsOver S} (h : X ⟶ Y) (k : Y ⟶ Z) :
    etaleModuleInverseImage k ⋙ etaleModuleInverseImage h ≅
      SheafOfModules.pushforward (etaleSiteHom_structureSheafMap_compData h k) :=
  SheafOfModules.pushforwardComp (etaleSiteHom h).structureSheafMap
    (etaleSiteHom k).structureSheafMap

/-- Transport of composite inverse image along the real total-functor composition
isomorphism. -/
def etaleModuleInverseImage_comp₁ {X Y Z : GroupoidsOver S} (h : X ⟶ Y) (k : Y ⟶ Z) :
    SheafOfModules.pushforward (etaleSiteHom_structureSheafMap_compData h k) ≅
      SheafOfModules.pushforward
        (etaleSiteHom_structureSheafMap_compData h k ≫
          (sheafPushforwardContinuousNatTrans
              (ObjectProperty.FullSubbicategory.toFunctor.compIso h k).hom
              RingCat.{u} X.etaleTopology Z.etaleTopology).app
            (etaleRingedSite Z).structureSheaf) :=
  SheafOfModules.pushforwardNatIso (etaleSiteHom_structureSheafMap_compData h k)
    (ObjectProperty.FullSubbicategory.toFunctor.compIso h k)

/-- The transported composite structure-sheaf map agrees with the structure-sheaf
map of the composite 1-morphism. -/
theorem etaleSiteHom_structureSheafMap_comp {X Y Z : GroupoidsOver S}
    (h : X ⟶ Y) (k : Y ⟶ Z) :
    etaleSiteHom_structureSheafMap_compData h k ≫
        (sheafPushforwardContinuousNatTrans
            (ObjectProperty.FullSubbicategory.toFunctor.compIso h k).hom
            RingCat.{u} X.etaleTopology Z.etaleTopology).app
          (etaleRingedSite Z).structureSheaf =
      (etaleSiteHom (h ≫ k)).structureSheafMap :=
  sorry

/-- Align the transported composite inverse image with inverse image along the
composite 1-morphism. -/
def etaleModuleInverseImage_comp₂ {X Y Z : GroupoidsOver S} (h : X ⟶ Y) (k : Y ⟶ Z) :
    SheafOfModules.pushforward
        (etaleSiteHom_structureSheafMap_compData h k ≫
          (sheafPushforwardContinuousNatTrans
              (ObjectProperty.FullSubbicategory.toFunctor.compIso h k).hom
              RingCat.{u} X.etaleTopology Z.etaleTopology).app
            (etaleRingedSite Z).structureSheaf) ≅
      etaleModuleInverseImage (h ≫ k) :=
  SheafOfModules.pushforwardCongr (etaleSiteHom_structureSheafMap_comp h k)

/-- Inverse image of étale modules along a composite 1-morphism is the composite
of the inverse images. -/
def etaleModuleInverseImage_comp {X Y Z : GroupoidsOver S} (h : X ⟶ Y) (k : Y ⟶ Z) :
    etaleModuleInverseImage k ⋙ etaleModuleInverseImage h ≅
      etaleModuleInverseImage (h ≫ k) :=
  etaleModuleInverseImage_comp₀ h k ≪≫
    etaleModuleInverseImage_comp₁ h k ≪≫ etaleModuleInverseImage_comp₂ h k

/-- The structure-sheaf map of `h₂` transported along `toFunctorIso e` agrees with
the structure-sheaf map of `h₁`. -/
theorem etaleSiteHom_structureSheafMap_iso {X Y : GroupoidsOver S} {h₁ h₂ : X ⟶ Y}
    (e : h₁ ≅ h₂) :
    (etaleSiteHom h₂).structureSheafMap ≫
        (sheafPushforwardContinuousNatTrans (toFunctorIso e).hom RingCat.{u}
            X.etaleTopology Y.etaleTopology).app
          (etaleRingedSite Y).structureSheaf =
      (etaleSiteHom h₁).structureSheafMap :=
  sorry

/-- Transport of inverse image along the real total-functor isomorphism. -/
def etaleModuleInverseImage_iso₀ {X Y : GroupoidsOver S} {h₁ h₂ : X ⟶ Y} (e : h₁ ≅ h₂) :
    etaleModuleInverseImage h₂ ≅
      SheafOfModules.pushforward
        ((etaleSiteHom h₂).structureSheafMap ≫
          (sheafPushforwardContinuousNatTrans (toFunctorIso e).hom RingCat.{u}
              X.etaleTopology Y.etaleTopology).app
            (etaleRingedSite Y).structureSheaf) :=
  SheafOfModules.pushforwardNatIso (etaleSiteHom h₂).structureSheafMap (toFunctorIso e)

/-- Align the transported inverse image with inverse image along `h₁`. -/
def etaleModuleInverseImage_iso₁ {X Y : GroupoidsOver S} {h₁ h₂ : X ⟶ Y} (e : h₁ ≅ h₂) :
    SheafOfModules.pushforward
        ((etaleSiteHom h₂).structureSheafMap ≫
          (sheafPushforwardContinuousNatTrans (toFunctorIso e).hom RingCat.{u}
              X.etaleTopology Y.etaleTopology).app
            (etaleRingedSite Y).structureSheaf) ≅
      etaleModuleInverseImage h₁ :=
  SheafOfModules.pushforwardCongr (etaleSiteHom_structureSheafMap_iso e)

/-- A 2-isomorphism of 1-morphisms induces an isomorphism of étale module
inverse images. -/
def etaleModuleInverseImage_iso {X Y : GroupoidsOver S} {h₁ h₂ : X ⟶ Y} (e : h₁ ≅ h₂) :
    etaleModuleInverseImage h₁ ≅ etaleModuleInverseImage h₂ :=
  (etaleModuleInverseImage_iso₀ e ≪≫ etaleModuleInverseImage_iso₁ e).symm

variable {X Y : GroupoidsOver S} {F G : AlgebraicSpace S}
variable (eX : F.toGroupoids ≌ X) (eY : G.toGroupoids ≌ Y) (f : X ⟶ Y)
variable (α : (f ≫ eY.symm.hom) ≅
    (eX.symm.hom ≫ AlgebraicSpace.toGroupoids.map (recoveredHom eX eY f)))

/-- Transport of the presentation `2`-iso `α` to
`eX.hom ≫ f ≅ map(recoveredHom) ≫ eY.hom` by units, counits, and associators. -/
def presentedTwoCell :
    eX.hom ≫ f ≅
      AlgebraicSpace.toGroupoids.map (recoveredHom eX eY f) ≫ eY.hom :=
  (ρ_ (eX.hom ≫ f)).symm ≪≫
    Bicategory.whiskerLeftIso (eX.hom ≫ f) eY.counit.symm ≪≫
    (α_ (eX.hom ≫ f) eY.inv eY.hom).symm ≪≫
    Bicategory.whiskerRightIso (α_ eX.hom f eY.inv) eY.hom ≪≫
    Bicategory.whiskerRightIso (Bicategory.whiskerLeftIso eX.hom α) eY.hom ≪≫
    Bicategory.whiskerRightIso
      (α_ eX.hom eX.inv
          (AlgebraicSpace.toGroupoids.map (recoveredHom eX eY f))).symm eY.hom ≪≫
    (α_ (eX.hom ≫ eX.inv)
        (AlgebraicSpace.toGroupoids.map (recoveredHom eX eY f)) eY.hom) ≪≫
    Bicategory.whiskerRightIso eX.unit.symm
      (AlgebraicSpace.toGroupoids.map (recoveredHom eX eY f) ≫ eY.hom) ≪≫
    λ_ (AlgebraicSpace.toGroupoids.map (recoveredHom eX eY f) ≫ eY.hom)

/-- Identification of `AlgebraicSpace.QCoh.pullback` with small-étale module
pullback on underlying module sheaves. -/
def restrict_pullback_toSpacePullback (𝒢 : QCoh Y) :
    ((AlgebraicSpace.QCoh.pullback (recoveredHom eX eY f)).obj
        ((QCoh.restrict eY).obj 𝒢)).obj ⟶
      (AlgebraicSpace.Modules.pullback (recoveredHom eX eY f)).obj
        ((QCoh.restrict eY).obj 𝒢).obj :=
  let _ := presentedTwoCell eX eY f α
  (ObjectProperty.FullSubcategory.restrict.compιIso
      (AlgebraicSpace.Modules.pullback (recoveredHom eX eY f))
      (fun _ hℱ =>
        AlgebraicSpace.Modules.pullback_quasiCoherentModuleProperty
          (recoveredHom eX eY f) hℱ)).hom.app
    ((QCoh.restrict eY).obj 𝒢)

/-- Reverse identification of small-étale module pullback with
`AlgebraicSpace.QCoh.pullback`. -/
def restrict_pullback_fromSpacePullback (𝒢 : QCoh Y) :
    (AlgebraicSpace.Modules.pullback (recoveredHom eX eY f)).obj
        ((QCoh.restrict eY).obj 𝒢).obj ⟶
      ((AlgebraicSpace.QCoh.pullback (recoveredHom eX eY f)).obj
        ((QCoh.restrict eY).obj 𝒢)).obj :=
  let _ := presentedTwoCell eX eY f α
  (ObjectProperty.FullSubcategory.restrict.compιIso
      (AlgebraicSpace.Modules.pullback (recoveredHom eX eY f))
      (fun _ hℱ =>
        AlgebraicSpace.Modules.pullback_quasiCoherentModuleProperty
          (recoveredHom eX eY f) hℱ)).inv.app
    ((QCoh.restrict eY).obj 𝒢)

/-- Transport of `𝒢` to an étale module on `G.toGroupoids` along `eY.hom`. -/
def restrict_pullback_toPresented (𝒢 : QCoh Y) :
    SheafOfModules.{u} (etaleRingedSite G.toGroupoids).structureSheaf :=
  let _ := presentedTwoCell eX eY f α
  (etaleModuleInverseImage eY.hom).obj ((toEtaleRingedModules Y).obj 𝒢.obj)

/-- Inverse image of the presented module along `toGroupoids.map (recoveredHom)`,
as site-level étale inverse image. -/
def restrict_pullback_presentedPullback (𝒢 : QCoh Y) :
    SheafOfModules.{u} (etaleRingedSite F.toGroupoids).structureSheaf :=
  (etaleModuleInverseImage
      (AlgebraicSpace.toGroupoids.map (recoveredHom eX eY f))).obj
    (restrict_pullback_toPresented eX eY f α 𝒢)

/-- Underlying type-valued comparison from geometric inverse image of the
presented module to continuous pushforward along `toFunctor (toGroupoids.map h)`. -/
def restrict_pullback_fromPullbackUnderlying (𝒢 : QCoh Y) :
    (ToInternal.underlying
          ((AlgebraicSpace.toGroupoidsEtaleRingedToposHom
              (recoveredHom eX eY f)).toTopos.ringInverseImage.obj
            (etaleRingedSite G.toGroupoids).structureSheaf)).obj
        (((AlgebraicSpace.toGroupoidsEtaleRingedToposHom
            (recoveredHom eX eY f)).toTopos.moduleInverseImage
            (etaleRingedSite G.toGroupoids).structureSheaf).obj
          (restrict_pullback_toPresented eX eY f α 𝒢)) ⟶
      (ToInternal.underlying
          ((AlgebraicSpace.toGroupoidsEtaleRingedToposHom
              (recoveredHom eX eY f)).toTopos.ringInverseImage.obj
            (etaleRingedSite G.toGroupoids).structureSheaf)).obj
        ((SheafOfModules.restrictScalars
            (AlgebraicSpace.toGroupoidsEtaleRingedToposHom
              (recoveredHom eX eY f)).structureMap).obj
          (restrict_pullback_presentedPullback eX eY f α 𝒢)) :=
  ((AlgebraicSpace.toGroupoidsEtaleRingedToposHom
        (recoveredHom eX eY f)).toTopos.moduleInverseImageForgetIso
        (etaleRingedSite G.toGroupoids).structureSheaf).hom.app
      (restrict_pullback_toPresented eX eY f α 𝒢) ≫
    (CartesianBasedFunctor.morphismOfTopoiIn.inverseImageComparison
        (toCartesianBasedFunctor
          (AlgebraicSpace.toGroupoids.map (recoveredHom eX eY f)))
        (StandardTopology.etale.overTopology S)).app
      ((ToInternal.underlying (etaleRingedSite G.toGroupoids).structureSheaf).obj
        (restrict_pullback_toPresented eX eY f α 𝒢)) ≫
      (sheafPushforwardContinuousIso
          (eqToIso
            (cartesian_toFunctor_eq
              (AlgebraicSpace.toGroupoids.map (recoveredHom eX eY f))))
          (Type u) F.toGroupoids.etaleTopology G.toGroupoids.etaleTopology).hom.app
        ((ToInternal.underlying (etaleRingedSite G.toGroupoids).structureSheaf).obj
          (restrict_pullback_toPresented eX eY f α 𝒢))

/-- Geometric inverse image of the presented module over `h⁻¹ 𝒪`, compared with
restriction of scalars of the site-level inverse image. -/
def restrict_pullback_fromPullback (𝒢 : QCoh Y) :
    ((AlgebraicSpace.toGroupoidsEtaleRingedToposHom
        (recoveredHom eX eY f)).toTopos.moduleInverseImage
        (etaleRingedSite G.toGroupoids).structureSheaf).obj
      (restrict_pullback_toPresented eX eY f α 𝒢) ⟶
      (SheafOfModules.restrictScalars
          (AlgebraicSpace.toGroupoidsEtaleRingedToposHom
            (recoveredHom eX eY f)).structureMap).obj
        (restrict_pullback_presentedPullback eX eY f α 𝒢) :=
  homOfUnderlying
    ((AlgebraicSpace.toGroupoidsEtaleRingedToposHom
        (recoveredHom eX eY f)).toTopos.ringInverseImage.obj
      (etaleRingedSite G.toGroupoids).structureSheaf)
    (restrict_pullback_fromPullbackUnderlying eX eY f α 𝒢) sorry sorry

/-- Topos-level module pullback compared with site-level inverse image along
`toGroupoids.map (recoveredHom)`. -/
def restrict_pullback_pullbackToInverseImage (𝒢 : QCoh Y) :
    (AlgebraicSpace.toGroupoidsEtaleRingedToposHom
        (recoveredHom eX eY f)).modulePullback.obj
      (restrict_pullback_toPresented eX eY f α 𝒢) ⟶
      restrict_pullback_presentedPullback eX eY f α 𝒢 :=
  (RingedSite.ToposHom.ModulePullback.scalarHomEquiv
      (AlgebraicSpace.toGroupoidsEtaleRingedToposHom (recoveredHom eX eY f))
      (((AlgebraicSpace.toGroupoidsEtaleRingedToposHom
          (recoveredHom eX eY f)).toTopos.moduleInverseImage
          (etaleRingedSite G.toGroupoids).structureSheaf).obj
        (restrict_pullback_toPresented eX eY f α 𝒢))
      (restrict_pullback_presentedPullback eX eY f α 𝒢)).symm
    (restrict_pullback_fromPullback eX eY f α 𝒢)

/-- Mate of `compareBigSmall_modules` along `pullbackPushforwardAdjunction`, after
transporting the topos unit along `restrict_pullback_pullbackToInverseImage`. -/
def restrict_pullback_presentedHom (𝒢 : QCoh Y) :
    (AlgebraicSpace.Modules.pullback (recoveredHom eX eY f)).obj
        ((AlgebraicSpace.restrictEtaleModules G).obj
          (restrict_pullback_toPresented eX eY f α 𝒢)) ⟶
      (AlgebraicSpace.restrictEtaleModules F).obj
        (restrict_pullback_presentedPullback eX eY f α 𝒢) :=
  ((AlgebraicSpace.Modules.pullbackPushforwardAdjunction
        (recoveredHom eX eY f)).homEquiv _ _).symm
    ((AlgebraicSpace.restrictEtaleModules G).map
        ((AlgebraicSpace.toGroupoidsEtaleRingedToposHom
            (recoveredHom eX eY f)).moduleAdjunction.unit.app
          (restrict_pullback_toPresented eX eY f α 𝒢) ≫
          (AlgebraicSpace.etaleModulePushforward (recoveredHom eX eY f)).map
            (restrict_pullback_pullbackToInverseImage eX eY f α 𝒢)) ≫
      (AlgebraicSpace.compareBigSmall_modules (recoveredHom eX eY f)
          (restrict_pullback_presentedPullback eX eY f α 𝒢)).hom)

/-- The identity-presentation pullback comparison is an isomorphism. -/
instance restrict_pullback_presentedHom_isIso (𝒢 : QCoh Y) :
    IsIso (restrict_pullback_presentedHom eX eY f α 𝒢) :=
  sorry

/-- Inverse of `restrict_pullback_presentedHom`. -/
def restrict_pullback_presentedInv (𝒢 : QCoh Y) :
    (AlgebraicSpace.restrictEtaleModules F).obj
        (restrict_pullback_presentedPullback eX eY f α 𝒢) ⟶
      (AlgebraicSpace.Modules.pullback (recoveredHom eX eY f)).obj
        ((AlgebraicSpace.restrictEtaleModules G).obj
          (restrict_pullback_toPresented eX eY f α 𝒢)) :=
  (@CategoryTheory.asIso _ _ _ _
      (restrict_pullback_presentedHom eX eY f α 𝒢)
      (restrict_pullback_presentedHom_isIso eX eY f α 𝒢)).inv

/-- Comparison of `π_{G,*}` with identity-presentation restriction, as the
composite module-pushforward isomorphism along `etaleSiteHom eY.hom` and `π_G`. -/
def restrict_pullback_restrictToPresented (𝒢 : QCoh Y) :
    ((etaleSiteHom eY.hom).modulePushforward ⋙
        (pi G G.toGroupoids (Bicategory.Equivalence.id G.toGroupoids)).modulePushforward).obj
      ((toEtaleRingedModules Y).obj 𝒢.obj) ⟶
      ((etaleSiteHom eY.hom).comp
          (pi G G.toGroupoids (Bicategory.Equivalence.id G.toGroupoids))).modulePushforward.obj
        ((toEtaleRingedModules Y).obj 𝒢.obj) :=
  let _ := presentedTwoCell eX eY f α
  (RingedSite.Hom.modulePushforwardCompIso
      (etaleSiteHom eY.hom)
      (pi G G.toGroupoids (Bicategory.Equivalence.id G.toGroupoids))).hom.app
    ((toEtaleRingedModules Y).obj 𝒢.obj)

/-- Reverse comparison of identity-presentation restriction with the composite
`π_{G,*}`. -/
def restrict_pullback_presentedToRestrict (𝒢 : QCoh Y) :
    ((etaleSiteHom eY.hom).comp
          (pi G G.toGroupoids (Bicategory.Equivalence.id G.toGroupoids))).modulePushforward.obj
        ((toEtaleRingedModules Y).obj 𝒢.obj) ⟶
      ((etaleSiteHom eY.hom).modulePushforward ⋙
        (pi G G.toGroupoids (Bicategory.Equivalence.id G.toGroupoids)).modulePushforward).obj
      ((toEtaleRingedModules Y).obj 𝒢.obj) :=
  let _ := presentedTwoCell eX eY f α
  (RingedSite.Hom.modulePushforwardCompIso
      (etaleSiteHom eY.hom)
      (pi G G.toGroupoids (Bicategory.Equivalence.id G.toGroupoids))).inv.app
    ((toEtaleRingedModules Y).obj 𝒢.obj)

/-- The base functor of `etaleSiteHom eY.hom ≫ π_G` agrees with the base of `π_G`. -/
theorem restrict_pullback_piComp_base :
    ((etaleSiteHom eY.hom).comp
        (pi G G.toGroupoids (Bicategory.Equivalence.id G.toGroupoids))).base =
      (pi G Y eY).base :=
  rfl

/-- Comparison of `π_{G,*}` with identity-presentation restriction. Restriction of
scalars along the two structure-sheaf maps of `π_G` and of `etaleSiteHom eY.hom ≫ π_G`
does not change the underlying abelian presheaf, so the comparison is the identity
on that presheaf. -/
def restrict_pullback_idPresented (𝒢 : QCoh Y) :
    ((QCoh.restrict eY).obj 𝒢).obj ⟶
      (AlgebraicSpace.restrictEtaleModules G).obj
        (restrict_pullback_toPresented eX eY f α 𝒢) :=
  { val :=
      PresheafOfModules.homMk
        (𝟙 ((QCoh.restrict eY).obj 𝒢).obj.val.presheaf) sorry }

/-- Reverse comparison of identity-presentation restriction with `π_{G,*}`. -/
def restrict_pullback_idPresentedInv (𝒢 : QCoh Y) :
    (AlgebraicSpace.restrictEtaleModules G).obj
        (restrict_pullback_toPresented eX eY f α 𝒢) ⟶
      ((QCoh.restrict eY).obj 𝒢).obj :=
  { val :=
      PresheafOfModules.homMk
        (𝟙 ((AlgebraicSpace.restrictEtaleModules G).obj
              (restrict_pullback_toPresented eX eY f α 𝒢)).val.presheaf) sorry }

/-- Identification of `QCoh.pullback f` with `modulePullback f` on underlying modules. -/
def restrict_pullback_toModulePullback (𝒢 : QCoh Y) :
    ((QCoh.pullback f).obj 𝒢).obj ⟶ (modulePullback f).obj 𝒢.obj :=
  let _ := presentedTwoCell eX eY f α
  (ObjectProperty.FullSubcategory.restrict.compιIso
      (modulePullback f) (modulePullback_le_inverseImage f)).hom.app 𝒢

/-- Reverse identification of `modulePullback f` with `QCoh.pullback f`. -/
def restrict_pullback_fromModulePullback (𝒢 : QCoh Y) :
    (modulePullback f).obj 𝒢.obj ⟶ ((QCoh.pullback f).obj 𝒢).obj :=
  let _ := presentedTwoCell eX eY f α
  (ObjectProperty.FullSubcategory.restrict.compιIso
      (modulePullback f) (modulePullback_le_inverseImage f)).inv.app 𝒢

/-- Identity-on-Γ transport intertwines CFG module pullback with étale inverse image. -/
def restrict_pullback_toEtaleCommute (𝒢 : QCoh Y) :
    (toEtaleRingedModules X).obj ((modulePullback f).obj 𝒢.obj) ⟶
      (etaleModuleInverseImage f).obj ((toEtaleRingedModules Y).obj 𝒢.obj) :=
  { val :=
      PresheafOfModules.homMk
        (𝟙 ((toEtaleRingedModules X).obj ((modulePullback f).obj 𝒢.obj)).val.presheaf)
        sorry }

/-- Reverse identity-on-Γ comparison of étale inverse image with CFG module pullback. -/
def restrict_pullback_toEtaleCommuteInv (𝒢 : QCoh Y) :
    (etaleModuleInverseImage f).obj ((toEtaleRingedModules Y).obj 𝒢.obj) ⟶
      (toEtaleRingedModules X).obj ((modulePullback f).obj 𝒢.obj) :=
  { val :=
      PresheafOfModules.homMk
        (𝟙 ((etaleModuleInverseImage f).obj
              ((toEtaleRingedModules Y).obj 𝒢.obj)).val.presheaf)
        sorry }

/-- `π_{F,eX,*}` of étale inverse image along `f` compared with identity-presentation
restriction of `eX.hom^*` of that inverse image. -/
def restrict_pullback_idLeftPresented (𝒢 : QCoh Y) :
    (restrictModules eX).obj
        ((etaleModuleInverseImage f).obj ((toEtaleRingedModules Y).obj 𝒢.obj)) ⟶
      (AlgebraicSpace.restrictEtaleModules F).obj
        ((etaleModuleInverseImage eX.hom).obj
          ((etaleModuleInverseImage f).obj ((toEtaleRingedModules Y).obj 𝒢.obj))) :=
  { val :=
      PresheafOfModules.homMk
        (𝟙 ((restrictModules eX).obj
              ((etaleModuleInverseImage f).obj
                ((toEtaleRingedModules Y).obj 𝒢.obj))).val.presheaf)
        sorry }

/-- Reverse of `restrict_pullback_idLeftPresented`. -/
def restrict_pullback_idLeftPresentedInv (𝒢 : QCoh Y) :
    (AlgebraicSpace.restrictEtaleModules F).obj
        ((etaleModuleInverseImage eX.hom).obj
          ((etaleModuleInverseImage f).obj ((toEtaleRingedModules Y).obj 𝒢.obj))) ⟶
      (restrictModules eX).obj
        ((etaleModuleInverseImage f).obj ((toEtaleRingedModules Y).obj 𝒢.obj)) :=
  { val :=
      PresheafOfModules.homMk
        (𝟙 ((AlgebraicSpace.restrictEtaleModules F).obj
              ((etaleModuleInverseImage eX.hom).obj
                ((etaleModuleInverseImage f).obj
                  ((toEtaleRingedModules Y).obj 𝒢.obj)))).val.presheaf)
        sorry }

/-- Comparison of `QCoh.restrict eX` of the CFG pullback with identity-presentation
restriction on `F`. -/
def restrict_pullback_idLeft (𝒢 : QCoh Y) :
    ((QCoh.restrict eX).obj ((QCoh.pullback f).obj 𝒢)).obj ⟶
      (AlgebraicSpace.restrictEtaleModules F).obj
        (restrict_pullback_presentedPullback eX eY f α 𝒢) :=
  (restrictModules eX).map
      ((toEtaleRingedModules X).map (restrict_pullback_toModulePullback eX eY f α 𝒢)) ≫
    (restrictModules eX).map (restrict_pullback_toEtaleCommute f 𝒢) ≫
      restrict_pullback_idLeftPresented eX f 𝒢 ≫
        (AlgebraicSpace.restrictEtaleModules F).map
          ((etaleModuleInverseImage_comp eX.hom f).hom.app
            ((toEtaleRingedModules Y).obj 𝒢.obj)) ≫
          (AlgebraicSpace.restrictEtaleModules F).map
            ((etaleModuleInverseImage_iso (presentedTwoCell eX eY f α)).hom.app
              ((toEtaleRingedModules Y).obj 𝒢.obj)) ≫
            (AlgebraicSpace.restrictEtaleModules F).map
              ((etaleModuleInverseImage_comp
                  (AlgebraicSpace.toGroupoids.map (recoveredHom eX eY f))
                  eY.hom).inv.app
                ((toEtaleRingedModules Y).obj 𝒢.obj))

/-- Reverse comparison on `F`. -/
def restrict_pullback_idLeftInv (𝒢 : QCoh Y) :
    (AlgebraicSpace.restrictEtaleModules F).obj
        (restrict_pullback_presentedPullback eX eY f α 𝒢) ⟶
      ((QCoh.restrict eX).obj ((QCoh.pullback f).obj 𝒢)).obj :=
  (AlgebraicSpace.restrictEtaleModules F).map
      ((etaleModuleInverseImage_comp
          (AlgebraicSpace.toGroupoids.map (recoveredHom eX eY f))
          eY.hom).hom.app
        ((toEtaleRingedModules Y).obj 𝒢.obj)) ≫
    (AlgebraicSpace.restrictEtaleModules F).map
      ((etaleModuleInverseImage_iso (presentedTwoCell eX eY f α)).inv.app
        ((toEtaleRingedModules Y).obj 𝒢.obj)) ≫
      (AlgebraicSpace.restrictEtaleModules F).map
        ((etaleModuleInverseImage_comp eX.hom f).inv.app
          ((toEtaleRingedModules Y).obj 𝒢.obj)) ≫
        restrict_pullback_idLeftPresentedInv eX f 𝒢 ≫
          (restrictModules eX).map (restrict_pullback_toEtaleCommuteInv f 𝒢) ≫
            (restrictModules eX).map
              ((toEtaleRingedModules X).map
                (restrict_pullback_fromModulePullback eX eY f α 𝒢))

/-- Module-level comparison of the two pullback-restriction composites. The
forward map is identity-on-Γ transport of CFG pullback, followed by the
identity-presentation mate of `compareBigSmall_modules`. -/
def restrict_pullback_modulesIso (𝒢 : QCoh Y) :
    ((QCoh.restrict eX).obj ((QCoh.pullback f).obj 𝒢)).obj ≅
      ((AlgebraicSpace.QCoh.pullback (recoveredHom eX eY f)).obj
        ((QCoh.restrict eY).obj 𝒢)).obj where
  hom :=
    restrict_pullback_idLeft eX eY f α 𝒢 ≫
      restrict_pullback_presentedInv eX eY f α 𝒢 ≫
        (AlgebraicSpace.Modules.pullback (recoveredHom eX eY f)).map
            (restrict_pullback_idPresentedInv eX eY f α 𝒢) ≫
          restrict_pullback_fromSpacePullback eX eY f α 𝒢
  inv :=
    restrict_pullback_toSpacePullback eX eY f α 𝒢 ≫
      (AlgebraicSpace.Modules.pullback (recoveredHom eX eY f)).map
          (restrict_pullback_idPresented eX eY f α 𝒢) ≫
        restrict_pullback_presentedHom eX eY f α 𝒢 ≫
          restrict_pullback_idLeftInv eX eY f α 𝒢
  hom_inv_id := sorry
  inv_hom_id := sorry

namespace QCoh

/-- Compatibility of `QCoh.restrict` with pullback along a 1-morphism of
categories fibred in groupoids represented by algebraic spaces. The
presentation 2-iso `α` records that `recoveredHom eX eY f` is the morphism of
algebraic spaces associated to `f`. -/
def restrict_pullbackComparison :
    pullback f ⋙ restrict eX ≅
      restrict eY ⋙ AlgebraicSpace.QCoh.pullback (recoveredHom eX eY f) :=
  NatIso.ofComponents
    (fun 𝒢 =>
      { hom := homMk (restrict_pullback_modulesIso eX eY f α 𝒢).hom
        inv := homMk (restrict_pullback_modulesIso eX eY f α 𝒢).inv
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

/-- The component of `restrict_pullbackComparison` is
`restrict_pullback_modulesIso`. -/
theorem restrict_pullbackComparison_hom_app (𝒢 : QCoh Y) :
    ((restrict_pullbackComparison eX eY f α).hom.app 𝒢).hom =
      (restrict_pullback_modulesIso eX eY f α 𝒢).hom :=
  rfl

end QCoh

end AlgebraicGeometry.GroupoidsOver
