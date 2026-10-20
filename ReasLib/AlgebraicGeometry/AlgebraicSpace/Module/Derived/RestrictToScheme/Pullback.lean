/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.RestrictToScheme
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pullback

/-! # Represented-scheme pullback and topology-change comparison

The square of ordinary direct images has explicit section maps in both directions. Its
adjoint inverse-image comparison and the displayed cell resolutions supply the source-facing
comparison on derived quasi-coherent complexes.
-/

@[expose] public section
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory CategoryTheory.Limits
open CategoryTheory.Sheaf.InternalModule
noncomputable section
universe u
namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.SchemeRestriction
variable {S : Scheme.{u}}

/-- The `Over S` morphism recovered from a morphism of algebraic spaces between schemes
over `S`. -/
def overHomOf {U V : Over S} (φ : ofOver U ⟶ ofOver V) : U ⟶ V :=
  Yoneda.fullyFaithful.preimage (φ : yoneda.obj U ⟶ yoneda.obj V)

/-- The scheme over `S` obtained by pulling an étale object of `ofOver U` back along `h.left`. -/
def ofOverSmallEtalePullbackOver {U V : Over S} (h : V ⟶ U)
    (W : smallEtaleSite (ofOver U)) : Over S :=
  Over.mk (pullback.fst h.left (overHomOf W.hom).left ≫ V.hom)

/-- Compatibility of the fibre-product projection with the structure morphisms over `S`. -/
theorem ofOverSmallEtalePullbackHom_w {U V : Over S} (h : V ⟶ U)
    (W : smallEtaleSite (ofOver U)) :
    pullback.fst h.left (overHomOf W.hom).left ≫ V.hom =
      (ofOverSmallEtalePullbackOver h W).hom :=
  rfl

/-- The morphism over `S` given by the first projection of the scheme fibre product. -/
def ofOverSmallEtalePullbackHom {U V : Over S} (h : V ⟶ U)
    (W : smallEtaleSite (ofOver U)) :
    ofOverSmallEtalePullbackOver h W ⟶ V :=
  Over.homMk (pullback.fst h.left (overHomOf W.hom).left)
    (ofOverSmallEtalePullbackHom_w h W)

/-- Pullback of an étale morphism of schemes over `S` remains étale. -/
instance instEtale_ofOverSmallEtalePullback {U V : Over S} (h : V ⟶ U)
    (W : smallEtaleSite (ofOver U)) :
    Etale (ofOverMap (ofOverSmallEtalePullbackHom h W)) :=
  sorry

/-- The object of the small étale site of `ofOver V` obtained by pulling `W` back along `h`. -/
def ofOverSmallEtalePullbackObj {U V : Over S} (h : V ⟶ U)
    (W : smallEtaleSite (ofOver U)) : smallEtaleSite (ofOver V) :=
  smallEtaleSite.mk (ofOverMap (ofOverSmallEtalePullbackHom h W))

/-- The morphism of fibre products induced by a morphism in the small étale site. -/
def ofOverSmallEtalePullbackMap {U V : Over S} (h : V ⟶ U)
    {W W' : smallEtaleSite (ofOver U)} (g : W' ⟶ W) :
    ofOverSmallEtalePullbackObj h W' ⟶ ofOverSmallEtalePullbackObj h W :=
  MorphismProperty.CostructuredArrow.homMk
    (Over.homMk
      (pullback.lift (pullback.fst h.left (overHomOf W'.hom).left)
        (pullback.snd h.left (overHomOf W'.hom).left ≫ g.left.left) sorry)
      sorry)
    trivial sorry

/-- Small étale pullback along a morphism of schemes over `S`. -/
def ofOverSmallEtalePullback {U V : Over S} (h : V ⟶ U) :
    smallEtaleSite (ofOver U) ⥤ smallEtaleSite (ofOver V) where
  obj := ofOverSmallEtalePullbackObj h
  map g := ofOverSmallEtalePullbackMap h g
  map_id := sorry
  map_comp := sorry

/-- Realization projection for `ofOverSmallEtalePullback h`, given by the second projection
of the scheme fibre product. -/
def ofOverEtaleProjection {U V : Over S} (h : V ⟶ U) :
    ofOverSmallEtalePullback h ⋙ smallEtaleToScheme (ofOver V) ⟶
      smallEtaleToScheme (ofOver U) where
  app W := pullback.snd h.left (overHomOf W.hom).left
  naturality _ _ _ := sorry

/-- Small étale pullback along a morphism of schemes over `S` is a morphism of sites. -/
instance instIsMorphismOfSites_ofOverSmallEtalePullback {U V : Over S} (h : V ⟶ U) :
    IsMorphismOfSites (smallEtaleTopology (ofOver U)) (smallEtaleTopology (ofOver V))
      (ofOverSmallEtalePullback h) :=
  sorry

/-- The morphism of small étale ringed sites induced by a morphism of schemes over `S`. -/
def ofOverRingedHom {U V : Over S} (h : V ⟶ U) :
    RingedSite.Hom (ringedSite (ofOver V)) (ringedSite (ofOver U)) :=
  Scheme.Site.ringedHom (smallEtaleTopology (ofOver U)) (smallEtaleTopology (ofOver V))
    (smallEtaleToScheme (ofOver U)) (smallEtaleToScheme (ofOver V))
    (ofOverSmallEtalePullback h) (ofOverEtaleProjection h)
    (structurePresheaf_isSheaf (ofOver U)) (structurePresheaf_isSheaf (ofOver V))

/-- The second projection of the scheme fibre product, as an arrow over the base. -/
def smallPullbackSndOver {U V : Over S} (h : V ⟶ U)
    (W : smallEtaleSite (ofOver U)) : ofOverSmallEtalePullbackOver h W ⟶ W.left :=
  Over.homMk (pullback.snd h.left (overHomOf W.hom).left) sorry

/-- The Yoneda map from the scheme pullback to the functor-of-points pullback. -/
def smallPullbackToSpace {U V : Over S} (h : V ⟶ U)
    (W : smallEtaleSite (ofOver U)) :
    ofOver (ofOverSmallEtalePullbackOver h W) ⟶ etaleBaseChangeSpace (ofOverMap h) W :=
  pullback.lift (f := homFunctor (ofOverMap h)) (g := homFunctor W.hom)
    (homFunctor (ofOverMap (ofOverSmallEtalePullbackHom h W)))
    (homFunctor (ofOverMap (smallPullbackSndOver h W))) sorry

/-- The inverse Yoneda comparison sends a compatible pair of points to its scheme pullback
lift. -/
def spacePullbackToSmall {U V : Over S} (h : V ⟶ U)
    (W : smallEtaleSite (ofOver U)) :
    etaleBaseChangeSpace (ofOverMap h) W ⟶ ofOver (ofOverSmallEtalePullbackOver h W) where
  app T := TypeCat.ofHom (fun x ↦
    (Over.homMk
      (pullback.lift (f := h.left) (g := (overHomOf W.hom).left)
        (((etaleBaseChangeFst (ofOverMap h) W).app T) x).left
        (((etaleBaseChangeSndNat (ofOverMap h) W).app T) x).left sorry) sorry :
      T.unop ⟶ ofOverSmallEtalePullbackOver h W))
  naturality := sorry

/-- The two fibre-product constructions agree over the source algebraic space. -/
def smallPullbackSpaceIso {U V : Over S} (h : V ⟶ U)
    (W : smallEtaleSite (ofOver U)) :
    (smallEtaleToSpaces (ofOver V)).obj (ofOverSmallEtalePullbackObj h W) ≅
      (etaleBaseChange (ofOverMap h)).obj W :=
  MorphismProperty.Over.isoMk
    { hom := smallPullbackToSpace h W
      inv := spacePullbackToSmall h W
      hom_inv_id := sorry
      inv_hom_id := sorry } sorry

/-- Evaluate the right Kan extension on the represented fibre product, then apply its counit. -/
def ofOverTypePushforwardComparison {U V : Over S} (h : V ⟶ U)
    (G : Sheaf (smallEtaleTopology (ofOver V)) (Type u)) :
    (typePushforward (ofOverMap h)).obj G ⟶
      ((ofOverSmallEtalePullback h).sheafPushforwardContinuous (Type u)
        (smallEtaleTopology (ofOver U)) (smallEtaleTopology (ofOver V))).obj G :=
  InducedCategory.homMk
    { app := fun W ↦
        EtaleTopos.extensionEvaluation (ofOver V) G (smallPullbackSpaceIso h W.unop).hom
      naturality := sorry }

/-- Direct-image comparison of algebraic-space pushforward with `ofOverRingedHom` pushforward,
induced by the pullback projection and the Kan counit. -/
def ofOverPushforwardHom {U V : Over S} (h : V ⟶ U) (G : (ofOver V).Modules) :
    (Modules.pushforward (ofOverMap h)).obj G ⟶
      (ofOverRingedHom h).modulePushforward.{u}.obj G :=
  homOfUnderlying (structureSheaf (ofOver U))
    ((RingedSite.ToposHom.ModulePushforward.forgetIso (ringedToposHom (ofOverMap h))).hom.app G ≫
      ofOverTypePushforwardComparison h
        ((ToInternal.underlying (structureSheaf (ofOver V))).obj G))
    sorry sorry

/-- Reverse evaluation first uses the actual inverse restriction counit and then transports
along the inverse represented-fibre-product map. -/
def ofOverTypePushforwardInverse {U V : Over S} (h : V ⟶ U)
    (G : Sheaf (smallEtaleTopology (ofOver V)) (Type u)) :
    ((ofOverSmallEtalePullback h).sheafPushforwardContinuous (Type u)
        (smallEtaleTopology (ofOver U)) (smallEtaleTopology (ofOver V))).obj G ⟶
      (typePushforward (ofOverMap h)).obj G :=
  InducedCategory.homMk
    { app := fun W ↦
        ((EtaleTopos.extensionRestrictionIso (ofOver V)).inv.app G).hom.app
            (Opposite.op (ofOverSmallEtalePullbackObj h W.unop)) ≫
          ((EtaleTopos.extension (ofOver V)).obj G).obj.map
            (smallPullbackSpaceIso h W.unop).inv.op
      naturality := sorry }

/-- Reverse module comparison with the actual extended-section function. -/
def ofOverPushforwardInv {U V : Over S} (h : V ⟶ U) (G : (ofOver V).Modules) :
    (ofOverRingedHom h).modulePushforward.{u}.obj G ⟶
      (Modules.pushforward (ofOverMap h)).obj G :=
  homOfUnderlying (structureSheaf (ofOver U))
    (ofOverTypePushforwardInverse h
        ((ToInternal.underlying (structureSheaf (ofOver V))).obj G) ≫
      (RingedSite.ToposHom.ModulePushforward.forgetIso (ringedToposHom (ofOverMap h))).inv.app G)
    sorry sorry

/-- Open restriction along a scheme morphism is a morphism of open-cover sites. -/
instance instIsMorphismOfSites_opensMap {X Y : Scheme.{u}} (φ : X ⟶ Y) :
    IsMorphismOfSites (Opens.grothendieckTopology (Y : TopCat))
      (Opens.grothendieckTopology (X : TopCat)) (TopologicalSpace.Opens.map φ.base) :=
  inferInstance

/-- Realization projection for `TopologicalSpace.Opens.map φ.base`, given by restriction of `φ` to an open. -/
def schemeOpensProjection {X Y : Scheme.{u}} (φ : X ⟶ Y) :
    TopologicalSpace.Opens.map φ.base ⋙ (X.restrictFunctor ⋙ Over.forget X) ⟶
      Y.restrictFunctor ⋙ Over.forget Y where
  app W := φ ∣_ W
  naturality _ _ _ := sorry

/-- The morphism of open-subscheme ringed sites induced by a scheme morphism. -/
def schemeOpensRingedHom {X Y : Scheme.{u}} (φ : X ⟶ Y) :
    RingedSite.Hom
      (RingedSite.ofRingSheaf (Opens.grothendieckTopology (X : TopCat))
        ⟨Scheme.Site.structurePresheaf (X.restrictFunctor ⋙ Over.forget X),
          opensStructurePresheaf_isSheaf X⟩)
      (RingedSite.ofRingSheaf (Opens.grothendieckTopology (Y : TopCat))
        ⟨Scheme.Site.structurePresheaf (Y.restrictFunctor ⋙ Over.forget Y),
          opensStructurePresheaf_isSheaf Y⟩) :=
  Scheme.Site.ringedHom (Opens.grothendieckTopology (Y : TopCat))
    (Opens.grothendieckTopology (X : TopCat))
    (Y.restrictFunctor ⋙ Over.forget Y) (X.restrictFunctor ⋙ Over.forget X)
    (TopologicalSpace.Opens.map φ.base) (schemeOpensProjection φ)
    (opensStructurePresheaf_isSheaf Y) (opensStructurePresheaf_isSheaf X)

/-- Both direct images evaluate the same module on the inverse-image open. The underlying maps
are identities; scalar compatibility is deferred. -/
def schemeOpensPushforwardIso {X Y : Scheme.{u}} (φ : X ⟶ Y) :
    (schemeOpensRingedHom φ).modulePushforward.{u} ⋙ opensToSchemeModules Y ≅
      opensToSchemeModules X ⋙ Scheme.Modules.pushforward φ :=
  NatIso.ofComponents
    (fun M ↦
      { hom := homOfUnderlying Y.ringCatSheaf
          (InducedCategory.homMk
            { app := fun _ ↦ 𝟙 _
              naturality := sorry }) sorry sorry
        inv := homOfUnderlying Y.ringCatSheaf
          (InducedCategory.homMk
            { app := fun _ ↦ 𝟙 _
              naturality := sorry }) sorry sorry
        hom_inv_id := sorry
        inv_hom_id := sorry }) sorry

/-- Identity-on-data comparison of scheme-module pushforward with ringed-space pushforward. -/
def schemePushforwardToRingedSpaceIso {X Y : Scheme.{u}} (φ : X ⟶ Y) :
    Scheme.Modules.pushforward φ ⋙ Scheme.Modules.toRingedSpace Y ≅
      Scheme.Modules.toRingedSpace X ⋙
        RingedSpace.Hom.pushforward φ.toLRSHom.toShHom :=
  NatIso.ofComponents
    (fun M ↦
      { hom := homOfUnderlying Y.toRingedSpace.ringCatSheaf
          (InducedCategory.homMk
            { app := fun _ ↦ 𝟙 _
              naturality := sorry }) sorry sorry
        inv := homOfUnderlying Y.toRingedSpace.ringCatSheaf
          (InducedCategory.homMk
            { app := fun _ ↦ 𝟙 _
              naturality := sorry }) sorry sorry
        hom_inv_id := sorry
        inv_hom_id := sorry }) sorry

/-- The two base functors in the restriction square are related by the scheme
pullback/open-restriction isomorphism. -/
def restrictPullbackBaseIso {U V : Over S} (h : V ⟶ U) :
    (RingedSite.Hom.comp (ofOverRingedHom h) (epsilon U)).base ≅
      (RingedSite.Hom.comp (epsilon V) (schemeOpensRingedHom h.left)).base :=
  NatIso.ofComponents
    (fun W ↦
      { hom := MorphismProperty.CostructuredArrow.homMk
          (Over.homMk (pullbackRestrictIsoRestrict h.left W).hom sorry)
          trivial sorry
        inv := MorphismProperty.CostructuredArrow.homMk
          (Over.homMk (pullbackRestrictIsoRestrict h.left W).inv sorry)
          trivial sorry
        hom_inv_id := sorry
        inv_hom_id := sorry }) sorry

/-- Continuity of the pullback-then-restriction presentation. -/
instance restrictPullbackLeft_isContinuous {U V : Over S} (h : V ⟶ U) :
    (RingedSite.Hom.comp (ofOverRingedHom h) (epsilon U)).base.IsContinuous
      (Opens.grothendieckTopology (U.left : TopCat)) (smallEtaleTopology (ofOver V)) :=
  RingedSite.Hom.base_isContinuous _

/-- Continuity of the restriction-then-pullback presentation. -/
instance restrictPullbackRight_isContinuous {U V : Over S} (h : V ⟶ U) :
    (RingedSite.Hom.comp (epsilon V) (schemeOpensRingedHom h.left)).base.IsContinuous
      (Opens.grothendieckTopology (U.left : TopCat)) (smallEtaleTopology (ofOver V)) :=
  RingedSite.Hom.base_isContinuous _

/-- The pullback/open-restriction isomorphism respects restriction of regular functions. -/
theorem restrictPullbackBaseIso_structure {U V : Over S} (h : V ⟶ U) :
    (RingedSite.Hom.comp (epsilon V) (schemeOpensRingedHom h.left)).structureSheafMap ≫
        (Functor.sheafPushforwardContinuousNatTrans (restrictPullbackBaseIso h).hom
          RingCat.{u} _ _).app (ringedSite (ofOver V)).structureSheaf =
      (RingedSite.Hom.comp (ofOverRingedHom h) (epsilon U)).structureSheafMap :=
  sorry

/-- Direct-image coherence for the restriction square, using the actual base-functor
isomorphism rather than equality of composite morphisms. -/
def restrictPullbackPushforwardIso {U V : Over S} (h : V ⟶ U) :
    (ofOverRingedHom h).modulePushforward.{u} ⋙ (epsilon U).modulePushforward.{u} ≅
      (epsilon V).modulePushforward.{u} ⋙
        (schemeOpensRingedHom h.left).modulePushforward.{u} :=
  RingedSite.Hom.modulePushforwardCompIso (ofOverRingedHom h) (epsilon U) ≪≫
    (SheafOfModules.pushforwardCongr₂
      (RingedSite.Hom.comp (epsilon V) (schemeOpensRingedHom h.left)).structureSheafMap
      (restrictPullbackBaseIso h) (restrictPullbackBaseIso_structure h)).symm ≪≫
    (RingedSite.Hom.modulePushforwardCompIso (epsilon V)
      (schemeOpensRingedHom h.left)).symm

/-- The direct-image square, assembled from the actual coefficient and chart comparisons. -/
def pushforwardSquareHom {U V : Over S} (h : V ⟶ U) :
    Modules.pushforward (ofOverMap h) ⋙ ordinary U ⟶
      ordinary V ⋙ RingedSpace.Hom.pushforward h.left.toLRSHom.toShHom where
  app G :=
    (ordinaryIso U).hom.app ((Modules.pushforward (ofOverMap h)).obj G) ≫
      (Scheme.Modules.toRingedSpace U.left).map
        ((opensToSchemeModules U.left).map
          ((epsilon U).modulePushforward.{u}.map (ofOverPushforwardHom h G))) ≫
      (Scheme.Modules.toRingedSpace U.left).map
        ((opensToSchemeModules U.left).map ((restrictPullbackPushforwardIso h).hom.app G)) ≫
      (Scheme.Modules.toRingedSpace U.left).map
        ((schemeOpensPushforwardIso h.left).hom.app ((epsilon V).modulePushforward.{u}.obj G)) ≫
      (schemePushforwardToRingedSpaceIso h.left).hom.app
        ((opensToSchemeModules V.left).obj ((epsilon V).modulePushforward.{u}.obj G)) ≫
      (RingedSpace.Hom.pushforward h.left.toLRSHom.toShHom).map ((ordinaryIso V).inv.app G)
  naturality := sorry

/-- Reverse direct-image comparison traverses those same actual section maps in reverse. -/
def pushforwardSquareInv {U V : Over S} (h : V ⟶ U) :
    ordinary V ⋙ RingedSpace.Hom.pushforward h.left.toLRSHom.toShHom ⟶
      Modules.pushforward (ofOverMap h) ⋙ ordinary U where
  app G :=
    (RingedSpace.Hom.pushforward h.left.toLRSHom.toShHom).map ((ordinaryIso V).hom.app G) ≫
      (schemePushforwardToRingedSpaceIso h.left).inv.app
        ((opensToSchemeModules V.left).obj ((epsilon V).modulePushforward.{u}.obj G)) ≫
      (Scheme.Modules.toRingedSpace U.left).map
        ((schemeOpensPushforwardIso h.left).inv.app ((epsilon V).modulePushforward.{u}.obj G)) ≫
      (Scheme.Modules.toRingedSpace U.left).map
        ((opensToSchemeModules U.left).map ((restrictPullbackPushforwardIso h).inv.app G)) ≫
      (Scheme.Modules.toRingedSpace U.left).map
        ((opensToSchemeModules U.left).map
          ((epsilon U).modulePushforward.{u}.map (ofOverPushforwardInv h G))) ≫
      (ordinaryIso U).inv.app ((Modules.pushforward (ofOverMap h)).obj G)
  naturality := sorry

/-- Both direct-image-square directions are the displayed chart and section maps. -/
def pushforwardSquareIso {U V : Over S} (h : V ⟶ U) :
    Modules.pushforward (ofOverMap h) ⋙ ordinary U ≅
      ordinary V ⋙ RingedSpace.Hom.pushforward h.left.toLRSHom.toShHom :=
  NatIso.ofComponents (fun G ↦
    { hom := (pushforwardSquareHom h).app G
      inv := (pushforwardSquareInv h).app G
      hom_inv_id := sorry
      inv_hom_id := sorry }) sorry

/-- The actual topology-change inverse images commute with ordinary scheme pullback, by
native uniqueness of the displayed composite adjunctions. -/
def epsilonPullbackSquareIso {U V : Over S} (h : V ⟶ U) :
    epsilonStar U ⋙ Modules.pullback (ofOverMap h) ≅
      RingedSpace.Hom.pullback h.left.toLRSHom.toShHom ⋙ epsilonStar V :=
  Adjunction.leftAdjointUniq
    ((adjunction U).comp (Modules.pullbackPushforwardAdjunction (ofOverMap h)))
    (((RingedSpace.Hom.pullbackPushforwardAdjunction h.left.toLRSHom.toShHom).comp
      (adjunction V)).ofNatIsoRight (pushforwardSquareIso h).symm)

/-- Compare actual étale cell models using the exact inverse image of the scheme-cell
augmentation; the map on both cell coordinates is the existing canonical cell-model map. -/
def pulledModelComparison {U V : Over S} (h : V ⟶ U)
    (A : CochainComplex U.left.toRingedSpace.Modules ℤ) :
    ((Modules.pullback (ofOverMap h)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (SheafOfModules.CellReplacement.model
          (((epsilonStar U).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (SheafOfModules.CellReplacement.model A))) ⟶
      ((Modules.pullback (ofOverMap h)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (SheafOfModules.CellReplacement.model
          (((epsilonStar U).mapHomologicalComplex (ComplexShape.up ℤ)).obj A)) :=
  ((Modules.pullback (ofOverMap h)).mapHomologicalComplex (ComplexShape.up ℤ)).map
    (SheafOfModules.CellReplacement.modelMap
      (((epsilonStar U).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (SheafOfModules.CellReplacement.augmentation A)))

/-- Exact inverse image preserves the scheme-cell augmentation quasi-isomorphism; the actual
étale pullback model functor preserves its resulting cell-model map. -/
theorem pulledModelComparison_quasiIso {U V : Over S} (h : V ⟶ U)
    (A : CochainComplex U.left.toRingedSpace.Modules ℤ) :
    QuasiIso (pulledModelComparison h A) := sorry

/-- The augmentation at the inverse image of the specified scheme-cell model, followed by
ordinary étale module pullback. -/
def pulledModelAugmentation {U V : Over S} (h : V ⟶ U)
    (A : CochainComplex U.left.toRingedSpace.Modules ℤ) :
    ((Modules.pullback (ofOverMap h)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (SheafOfModules.CellReplacement.model
          (((epsilonStar U).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (SheafOfModules.CellReplacement.model A))) ⟶
      ((Modules.pullback (ofOverMap h)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((epsilonStar U).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (SheafOfModules.CellReplacement.model A)) :=
  ((Modules.pullback (ofOverMap h)).mapHomologicalComplex (ComplexShape.up ℤ)).map
    (SheafOfModules.CellReplacement.augmentation
      (((epsilonStar U).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (SheafOfModules.CellReplacement.model A)))

/-- Inverse image of the specified flat-term K-flat model is K-flat with flat terms; ordinary
pullback preserves the displayed augmentation between these actual K-flat complexes. -/
theorem pulledModelAugmentation_quasiIso {U V : Over S} (h : V ⟶ U)
    (A : CochainComplex U.left.toRingedSpace.Modules ℤ) :
    QuasiIso (pulledModelAugmentation h A) := sorry

/-- The derived inverse-image square uses native cell computations, the two specified
quasi-isomorphisms, and the native ordinary inverse-image square, in both directions. -/
def epsilonPullbackSquareOnInput {U V : Over S} (h : V ⟶ U)
    (A : CochainComplex U.left.toRingedSpace.Modules ℤ) :
    (epsilonStarDerived U ⋙ ModuleDerived.pullback (ofOverMap h)).obj (DerivedCategory.Q.obj A) ≅
      (RingedSpace.modulePullbackDerived h.left.toLRSHom.toShHom ⋙ epsilonStarDerived V).obj
        (DerivedCategory.Q.obj A) :=
  (ModuleDerived.pullback (ofOverMap h)).mapIso
      ((epsilonStar U).mapDerivedCategoryFactors.app A) ≪≫
    (Modules.CellModels.pullbackUsingCells_fac (ofOverMap h)).app
      (((epsilonStar U).mapHomologicalComplex (ComplexShape.up ℤ)).obj A) ≪≫
    (Localization.isoOfHom (DerivedCategory.Q (C := (ofOver V).Modules))
      (HomologicalComplex.quasiIso (ofOver V).Modules (ComplexShape.up ℤ))
      (pulledModelComparison h A) (pulledModelComparison_quasiIso h A)).symm ≪≫
    Localization.isoOfHom (DerivedCategory.Q (C := (ofOver V).Modules))
      (HomologicalComplex.quasiIso (ofOver V).Modules (ComplexShape.up ℤ))
      (pulledModelAugmentation h A) (pulledModelAugmentation_quasiIso h A) ≪≫
    DerivedCategory.Q.mapIso
      ((Functor.mapHomologicalComplexCompIso (epsilonPullbackSquareIso h) (ComplexShape.up ℤ) ≪≫
        (Functor.mapHomologicalComplexCompIso
          (Iso.refl (RingedSpace.Hom.pullback h.left.toLRSHom.toShHom ⋙ epsilonStar V))
          (ComplexShape.up ℤ)).symm).app (SheafOfModules.CellReplacement.model A)) ≪≫
    ((epsilonStar V).mapDerivedCategoryFactors.app
      (((RingedSpace.Hom.pullback h.left.toLRSHom.toShHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (SheafOfModules.CellReplacement.model A))).symm ≪≫
    (epsilonStarDerived V).mapIso
      ((Functor.CellModel.fac (RingedSpace.Hom.pullback h.left.toLRSHom.toShHom)
        (RingedSpace.ModulePullbackCells.cochain_inverts h.left.toLRSHom.toShHom)).app A).symm ≪≫
    (epsilonStarDerived V).mapIso
      ((RingedSpace.modulePullbackDerivedCellIso h.left.toLRSHom.toShHom).app
        (DerivedCategory.Q.obj A))

/-- Each actual cochain comparison square is natural in the original cochain map. -/
theorem epsilonPullbackSquareOnInput_naturality {U V : Over S} (h : V ⟶ U)
    {A B : CochainComplex U.left.toRingedSpace.Modules ℤ} (a : A ⟶ B) :
    (DerivedCategory.Q ⋙ epsilonStarDerived U ⋙ ModuleDerived.pullback (ofOverMap h)).map a ≫
        (epsilonPullbackSquareOnInput h B).hom =
      (epsilonPullbackSquareOnInput h A).hom ≫
        (DerivedCategory.Q ⋙ RingedSpace.modulePullbackDerived h.left.toLRSHom.toShHom ⋙
          epsilonStarDerived V).map a := sorry

/-- Both inverse-image-square directions descend from their specified cochain-model paths. -/
def epsilonPullbackSquareOnCochains {U V : Over S} (h : V ⟶ U) :
    DerivedCategory.Q ⋙ epsilonStarDerived U ⋙ ModuleDerived.pullback (ofOverMap h) ≅
      DerivedCategory.Q ⋙ RingedSpace.modulePullbackDerived h.left.toLRSHom.toShHom ⋙
        epsilonStarDerived V :=
  NatIso.ofComponents (epsilonPullbackSquareOnInput h)
    (fun a ↦ epsilonPullbackSquareOnInput_naturality h a)

/-- Topology-change inverse image commutes with derived pullback along arbitrary scheme maps. -/
def epsilonPullbackDerivedIso {U V : Over S} (h : V ⟶ U) :
    epsilonStarDerived U ⋙ ModuleDerived.pullback (ofOverMap h) ≅
      RingedSpace.modulePullbackDerived h.left.toLRSHom.toShHom ⋙ epsilonStarDerived V :=
  Localization.liftNatIso (DerivedCategory.Q (C := U.left.toRingedSpace.Modules))
    (HomologicalComplex.quasiIso U.left.toRingedSpace.Modules (ComplexShape.up ℤ))
    (DerivedCategory.Q ⋙ epsilonStarDerived U ⋙ ModuleDerived.pullback (ofOverMap h))
    (DerivedCategory.Q ⋙ RingedSpace.modulePullbackDerived h.left.toLRSHom.toShHom ⋙
      epsilonStarDerived V)
    (epsilonStarDerived U ⋙ ModuleDerived.pullback (ofOverMap h))
    (RingedSpace.modulePullbackDerived h.left.toLRSHom.toShHom ⋙ epsilonStarDerived V)
    (epsilonPullbackSquareOnCochains h)

/-- Restricting the actual inverse-image square retains exactly its two ambient maps. -/
def epsilonPullbackQCohIso {U V : Over S} (h : V ⟶ U) :
    schemeToSpaceDerived U ⋙ DerivedQCoh.pullback (ofOverMap h) ≅
      Scheme.DerivedQCoh.pullback h.left ⋙ schemeToSpaceDerived V :=
  NatIso.ofComponents (fun A ↦ ObjectProperty.isoMk _ ((epsilonPullbackDerivedIso h).app A.obj))
    (by sorry)

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.SchemeRestriction

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
variable {S : Scheme.{u}}

/-- The ordinary restriction-pullback map is the mate of the actual direct-image square.
Its all-module source and target remain valid without an all-module invertibility claim. -/
def restrictPullbackUnderivedHom {U V : Over S} (h : V ⟶ U) :
    SchemeRestriction.ordinary U ⋙ RingedSpace.Hom.pullback h.left.toLRSHom.toShHom ⟶
      Modules.pullback (ofOverMap h) ⋙ SchemeRestriction.ordinary V :=
  ((mateEquiv (Modules.pullbackPushforwardAdjunction (ofOverMap h))
      (RingedSpace.Hom.pullbackPushforwardAdjunction h.left.toLRSHom.toShHom)).symm
    (SchemeRestriction.pushforwardSquareHom h)).natTrans

/-- The source's comparison at a derived quasi-coherent complex: use the displayed unit,
inverse-image square, and displayed counit. -/
def restrictPullbackComponent {U V : Over S} (h : V ⟶ U) (E : DerivedQCoh (ofOver U)) :
    (spaceToSchemeDerived U ⋙ Scheme.DerivedQCoh.pullback h.left).obj E ≅
      (pullback (ofOverMap h) ⋙ spaceToSchemeDerived V).obj E :=
  schemeRestrictionUnitComponent V
      ((Scheme.DerivedQCoh.pullback h.left).obj ((spaceToSchemeDerived U).obj E)) ≪≫
    (spaceToSchemeDerived V).mapIso
      ((SchemeRestriction.epsilonPullbackQCohIso h).app ((spaceToSchemeDerived U).obj E)).symm ≪≫
    (spaceToSchemeDerived V).mapIso
      ((pullback (ofOverMap h)).mapIso (schemeRestrictionCounitComponent U E))

/-- The displayed comparison is natural on the full derived quasi-coherent category. -/
theorem restrictPullbackComponent_naturality {U V : Over S} (h : V ⟶ U)
    {E F : DerivedQCoh (ofOver U)} (a : E ⟶ F) :
    (spaceToSchemeDerived U ⋙ Scheme.DerivedQCoh.pullback h.left).map a ≫
        (restrictPullbackComponent h F).hom =
      (restrictPullbackComponent h E).hom ≫
        (pullback (ofOverMap h) ⋙ spaceToSchemeDerived V).map a := sorry

/-- Right-derived restriction commutes with arbitrary derived scheme pullback on `D_QCoh`.
Both comparison directions are the actual unit, cell-model square and counit paths. -/
def restrictPullbackIso {U V : Over S} (h : V ⟶ U) :
    spaceToSchemeDerived U ⋙ Scheme.DerivedQCoh.pullback h.left ≅
      pullback (ofOverMap h) ⋙ spaceToSchemeDerived V :=
  NatIso.ofComponents (restrictPullbackComponent h)
    (fun a ↦ restrictPullbackComponent_naturality h a)

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
