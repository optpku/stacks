/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Adjunction
public import ReasLib.AlgebraicGeometry.RingedSite.Module.BaseChange
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pushforward.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ringed
public import ReasLib.CategoryTheory.Sites.Topos.ModuleAdjunction
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.CohomologyBaseChange.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.RingedSpace
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalLeftDerived
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalLeftDerived.Composition
public import stacks_project.Chap66.Lemma_66_26_3_Glueing
public import stacks_project.Chap66.Proposition_66_32_1_Comparison
public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh
public import stacks_project.Chap75.Lemma_75_21_1_Chart
public import stacks_project.Chap75.Lemma_75_26_6_Pullback

/-!
# Restriction of derived quasi-coherent complexes along étale scheme charts

Restriction along an étale scheme object `U → X` is derived pullback on the algebraic
space `ofOver U`, followed by the scheme identification `Modules.restrictToScheme` of
Proposition 66.32.1. This file does not import Remark 75.6.3: that path and
`pointCohomologyMap` both register `Modules.exactPullback_obj`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Limits
open CategoryTheory.Adjunction
open CategoryTheory.Sheaf.InternalModule
open ComplexShape TopologicalSpace
open Functor.LeftDerived.Homotopy
open Functor.LeftDerived.Homotopy.Composition

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

variable {S : Scheme.{u}}

/-- The composite of étale-to-scheme restriction with the identity-on-data comparison to
modules on the underlying ringed space is additive. -/
instance instAdditive_restrictToScheme_toRingedSpace (U : Over S) :
    (Modules.restrictToScheme U ⋙ Scheme.Modules.toRingedSpace U.left).Additive :=
  sorry

/-- The composite of étale-to-scheme restriction with the ringed-space comparison admits a
total left derived functor. -/
instance instHasLeftDerivedFunctor_restrictToScheme_toRingedSpace (U : Over S) :
    (Functor.Homotopy.toDerived
        (Modules.restrictToScheme U ⋙ Scheme.Modules.toRingedSpace U.left)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (Modules (ofOver U)) (up ℤ)) :=
  sorry

/-- Derived restriction from `D(𝒪_{ofOver U})` to `D(𝒪_{U.left})` on the underlying ringed
space, obtained by total left derived functor of `Modules.restrictToScheme` followed by
the identity-on-data comparison `Scheme.Modules.toRingedSpace`. -/
def spaceToSchemeDerived (U : Over S) :
    ModuleDerived (ofOver U) ⥤ RingedSpace.ModuleDerived U.left.toRingedSpace :=
  Functor.LeftDerived.Homotopy.functor
    (Modules.restrictToScheme U ⋙ Scheme.Modules.toRingedSpace U.left)

/-- `spaceToSchemeDerived` is the total left derived functor of étale-to-scheme restriction
composed with the ringed-space presentation functor. -/
theorem spaceToSchemeDerived_eq (U : Over S) :
    spaceToSchemeDerived U =
      Functor.LeftDerived.Homotopy.functor
        (Modules.restrictToScheme U ⋙ Scheme.Modules.toRingedSpace U.left) :=
  sorry

/-- The underived functor sending an `𝒪_{ofOver U}`-module to the ringed-space pullback of its
restriction to `U`, along a morphism of schemes over `S`. -/
abbrev restrictPullbackUnderivedLeft {U V : Over S} (h : V ⟶ U) :
    (ofOver U).Modules ⥤ V.left.toRingedSpace.Modules :=
  Modules.restrictToScheme U ⋙ Scheme.Modules.toRingedSpace U.left ⋙
    RingedSpace.Hom.pullback h.left.toLRSHom.toShHom

/-- `restrictPullbackUnderivedLeft` is restriction to `U`, the ringed-space presentation, then
ringed-space pullback. -/
theorem restrictPullbackUnderivedLeft_eq {U V : Over S} (h : V ⟶ U) :
    restrictPullbackUnderivedLeft h =
      Modules.restrictToScheme U ⋙ Scheme.Modules.toRingedSpace U.left ⋙
        RingedSpace.Hom.pullback h.left.toLRSHom.toShHom :=
  sorry

/-- The underived functor sending an `𝒪_{ofOver U}`-module to the restriction of its pullback
along `ofOverMap h`. -/
abbrev restrictPullbackUnderivedRight {U V : Over S} (h : V ⟶ U) :
    (ofOver U).Modules ⥤ V.left.toRingedSpace.Modules :=
  Modules.pullback (ofOverMap h) ⋙
    Modules.restrictToScheme V ⋙ Scheme.Modules.toRingedSpace V.left

/-- `restrictPullbackUnderivedRight` is algebraic-space pullback along `ofOverMap h` followed by
restriction to the underlying scheme of `V`. -/
theorem restrictPullbackUnderivedRight_eq {U V : Over S} (h : V ⟶ U) :
    restrictPullbackUnderivedRight h =
      Modules.pullback (ofOverMap h) ⋙
        Modules.restrictToScheme V ⋙ Scheme.Modules.toRingedSpace V.left :=
  sorry

/-- The ringed-site composite from the small étale site of `ofOver U` to the open-subscheme
ringed site of `U.left`. -/
def restrictToOpensHom (U : Over S) :
    RingedSite.Hom (ringedSite (ofOver U))
      (RingedSite.ofRingSheaf (Opens.grothendieckTopology (U.left : TopCat))
        ⟨Scheme.Site.structurePresheaf (U.left.restrictFunctor ⋙ Over.forget U.left),
          opensStructurePresheaf_isSheaf U.left⟩) :=
  RingedSite.Hom.comp (schemeEtaleRingedHom U) (smallEtaleToOpensRingedHom U.left)

/-- `restrictToOpensHom` is the composite of `schemeEtaleRingedHom` with
`smallEtaleToOpensRingedHom`. -/
theorem restrictToOpensHom_eq (U : Over S) :
    restrictToOpensHom U =
      RingedSite.Hom.comp (schemeEtaleRingedHom U) (smallEtaleToOpensRingedHom U.left) :=
  sorry

/-- Module pushforward along `schemeEtaleRingedHom` admits an inverse-image left adjoint. -/
instance instIsRightAdjoint_schemeEtaleRingedHom_modulePushforward (U : Over S) :
    ((schemeEtaleRingedHom U).modulePushforward.{u}).IsRightAdjoint :=
  sorry

/-- Module pushforward along `smallEtaleToOpensRingedHom` admits an inverse-image left adjoint. -/
instance instIsRightAdjoint_smallEtaleToOpensRingedHom_modulePushforward (X : Scheme.{u}) :
    ((smallEtaleToOpensRingedHom X).modulePushforward.{u}).IsRightAdjoint :=
  sorry

/-- Identification of the two-stage module pushforward in `restrictToScheme` with pushforward
along `restrictToOpensHom`. -/
def restrictToOpensPushforwardIso (U : Over S) :
    (schemeEtaleRingedHom U).modulePushforward.{u} ⋙
        (smallEtaleToOpensRingedHom U.left).modulePushforward.{u} ≅
      (restrictToOpensHom U).modulePushforward.{u} :=
  RingedSite.Hom.modulePushforwardCompIso.{u}
    (schemeEtaleRingedHom U) (smallEtaleToOpensRingedHom U.left)

/-- The two-stage étale-to-opens pushforward is `modulePushforward` of `restrictToOpensHom`. -/
theorem restrictToOpensPushforwardIso_eq (U : Over S) :
    restrictToOpensPushforwardIso U =
      RingedSite.Hom.modulePushforwardCompIso.{u}
        (schemeEtaleRingedHom U) (smallEtaleToOpensRingedHom U.left) :=
  sorry

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

/-- Module pushforward along `ofOverRingedHom` admits its canonical inverse-image left adjoint. -/
instance instIsRightAdjoint_ofOverRingedHom_modulePushforward {U V : Over S} (h : V ⟶ U) :
    ((ofOverRingedHom h).modulePushforward.{u}).IsRightAdjoint :=
  sorry

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
    (smallEtaleInclusion (ofOver V)).obj (ofOverSmallEtalePullbackObj h W) ≅
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

/-- Open restriction along a scheme morphism is a morphism of open-cover sites. -/
instance instIsMorphismOfSites_opensMap {X Y : Scheme.{u}} (φ : X ⟶ Y) :
    IsMorphismOfSites (Opens.grothendieckTopology (Y : TopCat))
      (Opens.grothendieckTopology (X : TopCat)) (Opens.map φ.base) :=
  inferInstance

/-- Realization projection for `Opens.map φ.base`, given by restriction of `φ` to an open. -/
def schemeOpensProjection {X Y : Scheme.{u}} (φ : X ⟶ Y) :
    Opens.map φ.base ⋙ (X.restrictFunctor ⋙ Over.forget X) ⟶
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
    (Opens.map φ.base) (schemeOpensProjection φ)
    (opensStructurePresheaf_isSheaf Y) (opensStructurePresheaf_isSheaf X)

/-- Module pushforward along `schemeOpensRingedHom` admits its canonical inverse-image left
adjoint. -/
instance instIsRightAdjoint_schemeOpensRingedHom_modulePushforward {X Y : Scheme.{u}}
    (φ : X ⟶ Y) :
    ((schemeOpensRingedHom φ).modulePushforward.{u}).IsRightAdjoint :=
  sorry

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
    (RingedSite.Hom.comp (ofOverRingedHom h) (restrictToOpensHom U)).base ≅
      (RingedSite.Hom.comp (restrictToOpensHom V) (schemeOpensRingedHom h.left)).base :=
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
    (RingedSite.Hom.comp (ofOverRingedHom h) (restrictToOpensHom U)).base.IsContinuous
      (Opens.grothendieckTopology (U.left : TopCat)) (smallEtaleTopology (ofOver V)) :=
  RingedSite.Hom.base_isContinuous _

/-- Continuity of the restriction-then-pullback presentation. -/
instance restrictPullbackRight_isContinuous {U V : Over S} (h : V ⟶ U) :
    (RingedSite.Hom.comp (restrictToOpensHom V) (schemeOpensRingedHom h.left)).base.IsContinuous
      (Opens.grothendieckTopology (U.left : TopCat)) (smallEtaleTopology (ofOver V)) :=
  RingedSite.Hom.base_isContinuous _

/-- The pullback/open-restriction isomorphism respects restriction of regular functions. -/
theorem restrictPullbackBaseIso_structure {U V : Over S} (h : V ⟶ U) :
    (RingedSite.Hom.comp (restrictToOpensHom V) (schemeOpensRingedHom h.left)).structureSheafMap ≫
        (Functor.sheafPushforwardContinuousNatTrans (restrictPullbackBaseIso h).hom
          RingCat.{u} _ _).app (ringedSite (ofOver V)).structureSheaf =
      (RingedSite.Hom.comp (ofOverRingedHom h) (restrictToOpensHom U)).structureSheafMap :=
  sorry

/-- Direct-image coherence for the restriction square, using the actual base-functor
isomorphism rather than equality of composite morphisms. -/
def restrictPullbackPushforwardIso {U V : Over S} (h : V ⟶ U) :
    (ofOverRingedHom h).modulePushforward.{u} ⋙ (restrictToOpensHom U).modulePushforward.{u} ≅
      (restrictToOpensHom V).modulePushforward.{u} ⋙
        (schemeOpensRingedHom h.left).modulePushforward.{u} :=
  RingedSite.Hom.modulePushforwardCompIso (ofOverRingedHom h) (restrictToOpensHom U) ≪≫
    (SheafOfModules.pushforwardCongr₂
      (RingedSite.Hom.comp (restrictToOpensHom V) (schemeOpensRingedHom h.left)).structureSheafMap
      (restrictPullbackBaseIso h) (restrictPullbackBaseIso_structure h)).symm ≪≫
    (RingedSite.Hom.modulePushforwardCompIso (restrictToOpensHom V)
      (schemeOpensRingedHom h.left)).symm

/-- Unfold `restrictToScheme` along the two-stage étale-to-opens pushforward isomorphism. -/
def restrictToSchemeUnfold {U : Over S} (G : (ofOver U).Modules) :
    (Scheme.Modules.toRingedSpace U.left).obj ((Modules.restrictToScheme U).obj G) ⟶
      (Scheme.Modules.toRingedSpace U.left).obj
        ((opensToSchemeModules U.left).obj
          ((restrictToOpensHom U).modulePushforward.{u}.obj
            ((Modules.restrictFunctor (𝟙 (ofOver U))).obj G))) :=
  (Scheme.Modules.toRingedSpace U.left).map
    ((opensToSchemeModules U.left).map
      ((restrictToOpensPushforwardIso U).hom.app
        ((Modules.restrictFunctor (𝟙 (ofOver U))).obj G)))

/-- Refold `restrictToScheme` along the two-stage étale-to-opens pushforward isomorphism. -/
def restrictToSchemeFold {U : Over S} (G : (ofOver U).Modules) :
    (Scheme.Modules.toRingedSpace U.left).obj
        ((opensToSchemeModules U.left).obj
          ((restrictToOpensHom U).modulePushforward.{u}.obj
            ((Modules.restrictFunctor (𝟙 (ofOver U))).obj G))) ⟶
      (Scheme.Modules.toRingedSpace U.left).obj ((Modules.restrictToScheme U).obj G) :=
  (Scheme.Modules.toRingedSpace U.left).map
    ((opensToSchemeModules U.left).map
      ((restrictToOpensPushforwardIso U).inv.app
        ((Modules.restrictFunctor (𝟙 (ofOver U))).obj G)))

/-- Restriction of algebraic-space pushforward compared with Zariski pushforward of
restriction, after the `schemeEtaleRingedHom`/`smallEtaleToOpensRingedHom`/`opensToSchemeModules`
presentation of `restrictToScheme`. -/
def restrictPushforwardUnderivedHom {U V : Over S} (h : V ⟶ U) :
    Modules.pushforward (ofOverMap h) ⋙
        Modules.restrictToScheme U ⋙ Scheme.Modules.toRingedSpace U.left ⟶
      Modules.restrictToScheme V ⋙ Scheme.Modules.toRingedSpace V.left ⋙
        RingedSpace.Hom.pushforward h.left.toLRSHom.toShHom where
  app G :=
    restrictToSchemeUnfold ((Modules.pushforward (ofOverMap h)).obj G) ≫
      (Scheme.Modules.toRingedSpace U.left).map
        ((opensToSchemeModules U.left).map
          ((restrictToOpensHom U).modulePushforward.{u}.map
            ((SmallEtaleModuleGlueing.restrictFunctorId (ofOver U)).hom.app
              ((Modules.pushforward (ofOverMap h)).obj G)))) ≫
      (Scheme.Modules.toRingedSpace U.left).map
        ((opensToSchemeModules U.left).map
          ((restrictToOpensHom U).modulePushforward.{u}.map
            (ofOverPushforwardHom h G))) ≫
      (Scheme.Modules.toRingedSpace U.left).map
        ((opensToSchemeModules U.left).map
          ((restrictPullbackPushforwardIso h).hom.app G)) ≫
      (Scheme.Modules.toRingedSpace U.left).map
        ((schemeOpensPushforwardIso h.left).hom.app
          ((restrictToOpensHom V).modulePushforward.{u}.obj G)) ≫
      (schemePushforwardToRingedSpaceIso h.left).hom.app
        ((opensToSchemeModules V.left).obj
          ((restrictToOpensHom V).modulePushforward.{u}.obj G)) ≫
      (RingedSpace.Hom.pushforward h.left.toLRSHom.toShHom).map
        ((Scheme.Modules.toRingedSpace V.left).map
          ((opensToSchemeModules V.left).map
            ((restrictToOpensHom V).modulePushforward.{u}.map
              ((SmallEtaleModuleGlueing.restrictFunctorId (ofOver V)).inv.app G)))) ≫
      (RingedSpace.Hom.pushforward h.left.toLRSHom.toShHom).map
        (restrictToSchemeFold G)
  naturality := sorry

/-- Forward comparison from restriction-then-Zariski-pullback to étale-pullback-then-restriction.
This is the mate of `restrictPushforwardUnderivedHom` under the algebraic-space and
ringed-space pullback-pushforward adjunctions. -/
def restrictPullbackUnderivedHom {U V : Over S} (h : V ⟶ U) :
    restrictPullbackUnderivedLeft h ⟶ restrictPullbackUnderivedRight h :=
  ((mateEquiv
      (Modules.pullbackPushforwardAdjunction (ofOverMap h))
      (RingedSpace.Hom.pullbackPushforwardAdjunction h.left.toLRSHom.toShHom)).symm
    (restrictPushforwardUnderivedHom h)).natTrans

/-- The forward comparison of restriction and pullback is invertible. -/
instance instIsIso_restrictPullbackUnderivedHom {U V : Over S} (h : V ⟶ U) :
    IsIso (restrictPullbackUnderivedHom h) :=
  sorry

/-- Underived restriction to the underlying scheme commutes with pullback along a morphism of
schemes over `S`. -/
def restrictPullbackUnderivedIso {U V : Over S} (h : V ⟶ U) :
    restrictPullbackUnderivedLeft h ≅ restrictPullbackUnderivedRight h :=
  asIso (restrictPullbackUnderivedHom h)

/-- The underived commutation isomorphism is the named unit/counit comparison. -/
theorem restrictPullbackUnderivedIso_hom {U V : Over S} (h : V ⟶ U) :
    (restrictPullbackUnderivedIso h).hom = restrictPullbackUnderivedHom h :=
  sorry

/-- Restriction then ringed-space pullback is additive. -/
instance instAdditive_restrictPullbackUnderivedLeft {U V : Over S} (h : V ⟶ U) :
    (restrictPullbackUnderivedLeft h).Additive :=
  sorry

/-- Pullback then restriction to the underlying scheme is additive. -/
instance instAdditive_restrictPullbackUnderivedRight {U V : Over S} (h : V ⟶ U) :
    (restrictPullbackUnderivedRight h).Additive :=
  sorry

/-- Restriction then ringed-space pullback admits a total left derived functor. -/
instance instHasLeftDerivedFunctor_restrictPullbackUnderivedLeft {U V : Over S}
    (h : V ⟶ U) :
    (Functor.Homotopy.toDerived (restrictPullbackUnderivedLeft h)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (Modules (ofOver U)) (up ℤ)) :=
  sorry

/-- Pullback then restriction to the underlying scheme admits a total left derived functor. -/
instance instHasLeftDerivedFunctor_restrictPullbackUnderivedRight {U V : Over S}
    (h : V ⟶ U) :
    (Functor.Homotopy.toDerived (restrictPullbackUnderivedRight h)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (Modules (ofOver U)) (up ℤ)) :=
  sorry

/-- The composition comparison for restriction then ringed-space pullback is invertible. -/
instance instIsIso_restrictPullbackComparison_left {U V : Over S} (h : V ⟶ U) :
    IsIso
      (comparison (RingedSpace.Hom.pullback h.left.toLRSHom.toShHom)
        (Modules.restrictToScheme U ⋙ Scheme.Modules.toRingedSpace U.left)
        (restrictPullbackUnderivedLeft h) (Iso.refl _)) :=
  sorry

/-- The composition comparison for pullback then restriction is invertible. -/
instance instIsIso_restrictPullbackComparison_right {U V : Over S} (h : V ⟶ U) :
    IsIso
      (comparison (Modules.restrictToScheme V ⋙ Scheme.Modules.toRingedSpace V.left)
        (Modules.pullback (ofOverMap h)) (restrictPullbackUnderivedRight h)
        (Iso.refl _)) :=
  sorry

/-- Restriction of derived modules to the underlying scheme commutes with pullback along a
morphism of schemes over `S`. -/
def restrictPullbackIso {U V : Over S} (h : V ⟶ U) :
    spaceToSchemeDerived U ⋙
        RingedSpace.modulePullbackDerived h.left.toLRSHom.toShHom ≅
      ModuleDerived.pullback (ofOverMap h) ⋙ spaceToSchemeDerived V :=
  iso (RingedSpace.Hom.pullback h.left.toLRSHom.toShHom)
      (Modules.restrictToScheme U ⋙ Scheme.Modules.toRingedSpace U.left)
      (restrictPullbackUnderivedLeft h) (Iso.refl _) ≪≫
    Functor.leftDerivedNatIso
      (functor (restrictPullbackUnderivedLeft h))
      (functor (restrictPullbackUnderivedRight h))
      (counit (restrictPullbackUnderivedLeft h))
      (counit (restrictPullbackUnderivedRight h))
      (HomotopyCategory.quasiIso (Modules (ofOver U)) (up ℤ))
      (Functor.isoWhiskerRight
        (Functor.mapHomotopyCategoryIso (restrictPullbackUnderivedIso h))
        DerivedCategory.Qh) ≪≫
    (iso (Modules.restrictToScheme V ⋙ Scheme.Modules.toRingedSpace V.left)
        (Modules.pullback (ofOverMap h)) (restrictPullbackUnderivedRight h)
        (Iso.refl _)).symm

/-- `restrictPullbackIso` is the composition comparison of ringed-space pullback after
restriction, transported across the underived commutation isomorphism. -/
theorem restrictPullbackIso_eq {U V : Over S} (h : V ⟶ U) :
    restrictPullbackIso h =
      iso (RingedSpace.Hom.pullback h.left.toLRSHom.toShHom)
          (Modules.restrictToScheme U ⋙ Scheme.Modules.toRingedSpace U.left)
          (restrictPullbackUnderivedLeft h) (Iso.refl _) ≪≫
        Functor.leftDerivedNatIso
          (functor (restrictPullbackUnderivedLeft h))
          (functor (restrictPullbackUnderivedRight h))
          (counit (restrictPullbackUnderivedLeft h))
          (counit (restrictPullbackUnderivedRight h))
          (HomotopyCategory.quasiIso (Modules (ofOver U)) (up ℤ))
          (Functor.isoWhiskerRight
            (Functor.mapHomotopyCategoryIso (restrictPullbackUnderivedIso h))
            DerivedCategory.Qh) ≪≫
        (iso (Modules.restrictToScheme V ⋙ Scheme.Modules.toRingedSpace V.left)
            (Modules.pullback (ofOverMap h)) (restrictPullbackUnderivedRight h)
            (Iso.refl _)).symm :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

/-- Derived pullback along equal morphisms of algebraic spaces is isomorphic. -/
def pullbackCongr {S : Scheme.{u}} {Y X : AlgebraicSpace S} {f g : Y ⟶ X} (h : f = g) :
    pullback f ≅ pullback g :=
  eqToIso (congrArg pullback h)

/-- `pullbackCongr` is the functoriality of derived pullback on equal morphisms. -/
theorem pullbackCongr_eq {S : Scheme.{u}} {Y X : AlgebraicSpace S} {f g : Y ⟶ X}
    (h : f = g) : pullbackCongr h = eqToIso (congrArg pullback h) :=
  sorry

/-- The canonical comparison from iterated derived pullback to derived pullback along the
composite morphism is invertible. -/
instance instIsIso_pullbackCompComparison {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ Z) (g : Z ⟶ X) : IsIso (pullbackCompComparison f g) :=
  sorry

/-- The canonical isomorphism from iterated derived pullback to derived pullback along the
composite morphism. -/
def pullbackCompIso {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ Z) (g : Z ⟶ X) :
    pullback g ⋙ pullback f ≅ pullback (f ≫ g) :=
  asIso (pullbackCompComparison f g)

/-- The forward map of `pullbackCompIso` is the canonical composition comparison. -/
theorem pullbackCompIso_hom {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ Z) (g : Z ⟶ X) :
    (pullbackCompIso f g).hom = pullbackCompComparison f g :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

variable {S : Scheme.{u}}
variable {X' X Y' Y : AlgebraicSpace S}
variable {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

namespace EtaleBaseChangeChart

/-- Restriction of a quasi-coherent complex along `U → X` remains quasi-coherent on `U`. -/
theorem restrict_mapsTo (c : EtaleBaseChangeChart g' f' f g) (K : DerivedQCoh X) :
    Scheme.derivedQuasiCoherentModuleProperty c.U.left.left
      ((spaceToSchemeDerived c.U.left).obj
        ((ModuleDerived.pullback c.U.hom).obj ((inclusion X).obj K))) :=
  sorry

/-- The restriction `(U → X)^* K` as an object of `D_QCoh` on the underlying scheme of `U`. -/
def restrict (c : EtaleBaseChangeChart g' f' f g) (K : DerivedQCoh X) :
    Scheme.DerivedQCoh c.U.left.left where
  obj := (spaceToSchemeDerived c.U.left).obj
    ((ModuleDerived.pullback c.U.hom).obj ((inclusion X).obj K))
  property := c.restrict_mapsTo K

/-- `restrict` is derived restriction of ambient pullback along `U → X`. -/
theorem restrict_eq (c : EtaleBaseChangeChart g' f' f g) (K : DerivedQCoh X) :
    (c.restrict K).obj =
      (spaceToSchemeDerived c.U.left).obj
        ((ModuleDerived.pullback c.U.hom).obj ((inclusion X).obj K)) :=
  sorry

/-- Restriction of a quasi-coherent complex along `U' → X'` remains quasi-coherent on `U'`. -/
theorem restrictK'_mapsTo (c : EtaleBaseChangeChart g' f' f g) (sq : IsPullback g' f' f g)
    (K' : DerivedQCoh X') :
    Scheme.derivedQuasiCoherentModuleProperty c.schemeU'
      ((spaceToSchemeDerived c.U'Over).obj
        ((ModuleDerived.pullback (c.toX' sq)).obj ((inclusion X').obj K'))) :=
  sorry

/-- The restriction `(U' → X')^* K'` as an object of `D_QCoh` on the scheme `U'`. -/
def restrictK' (c : EtaleBaseChangeChart g' f' f g) (sq : IsPullback g' f' f g)
    (K' : DerivedQCoh X') : Scheme.DerivedQCoh c.schemeU' where
  obj := (spaceToSchemeDerived c.U'Over).obj
    ((ModuleDerived.pullback (c.toX' sq)).obj ((inclusion X').obj K'))
  property := c.restrictK'_mapsTo sq K'

/-- Ambient derived morphism underlying the restricted scheme-square map, obtained by
transporting `L(U' → X')^* α` along `pullback.inclusionIso`, `restrictPullbackIso`, and the
composition comparisons for `toX' ≫ g'` and `ofOverMap toUOver ≫ U.hom`. -/
def restrictMap_toAmbient (c : EtaleBaseChangeChart g' f' f g) (sq : IsPullback g' f' f g)
    (K : DerivedQCoh X) (K' : DerivedQCoh X')
    (α : (ModuleDerived.pullback g').obj ((inclusion X).obj K) ⟶ (inclusion X').obj K') :
    ((Scheme.DerivedQCoh.inclusion c.schemeU').obj
        ((Scheme.DerivedQCoh.pullback c.fst).obj (c.restrict K))) ⟶
      ((Scheme.DerivedQCoh.inclusion c.schemeU').obj (c.restrictK' sq K')) :=
  (Scheme.DerivedQCoh.pullback.inclusionIso c.fst).hom.app (c.restrict K) ≫
    (restrictPullbackIso c.toUOver).hom.app
      ((ModuleDerived.pullback c.U.hom).obj ((inclusion X).obj K)) ≫
    (spaceToSchemeDerived c.U'Over).map
      ((ModuleDerived.pullbackCompIso (ofOverMap c.toUOver) c.U.hom).hom.app
        ((inclusion X).obj K)) ≫
    (spaceToSchemeDerived c.U'Over).map
      ((ModuleDerived.pullbackCongr (c.toX'_comp_g' sq)).inv.app
        ((inclusion X).obj K)) ≫
    (spaceToSchemeDerived c.U'Over).map
      ((ModuleDerived.pullbackCompIso (c.toX' sq) g').inv.app ((inclusion X).obj K) ≫
        (ModuleDerived.pullback (c.toX' sq)).map α)

/-- The restricted map `L(U' → U)^* (U → X)^* K ⟶ (U' → X')^* K'` on the scheme square. -/
def restrictMap (c : EtaleBaseChangeChart g' f' f g) (sq : IsPullback g' f' f g)
    (K : DerivedQCoh X) (K' : DerivedQCoh X')
    (α : (ModuleDerived.pullback g').obj ((inclusion X).obj K) ⟶ (inclusion X').obj K') :
    (Scheme.DerivedQCoh.pullback c.fst).obj (c.restrict K) ⟶ c.restrictK' sq K' :=
  ObjectProperty.homMk (c.restrictMap_toAmbient sq K K' α)

/-- `restrictMap` is the full-subcategory morphism associated to `restrictMap_toAmbient`. -/
theorem restrictMap_spec (c : EtaleBaseChangeChart g' f' f g) (sq : IsPullback g' f' f g)
    (K : DerivedQCoh X) (K' : DerivedQCoh X')
    (α : (ModuleDerived.pullback g').obj ((inclusion X).obj K) ⟶ (inclusion X').obj K') :
    ((Scheme.DerivedQCoh.inclusion c.schemeU').map (c.restrictMap sq K K' α)) =
      c.restrictMap_toAmbient sq K K' α :=
  sorry

/-- Lemma 36.26.1 holds on the restricted scheme square of an étale chart. -/
def schemeHolds (c : EtaleBaseChangeChart g' f' f g) (sq : IsPullback g' f' f g)
    (K : DerivedQCoh X) (K' : DerivedQCoh X')
    (α : (ModuleDerived.pullback g').obj ((inclusion X).obj K) ⟶ (inclusion X').obj K') :
    Prop :=
  ∀ (x' : c.schemeU') (i : ℤ),
    IsIso
      ((Scheme.DerivedQCoh.CohomologyBaseChangeModel.canonical
          c.fst c.snd c.mapU.left c.mapV'.left c.schemeIsPullback).pointMap
        (c.restrict K) (c.restrictK' sq K') (c.restrictMap sq K K' α) x' i)

/-- `schemeHolds` is the pointwise isomorphism clause of Lemma 36.26.1 on the chart. -/
theorem schemeHolds_iff (c : EtaleBaseChangeChart g' f' f g) (sq : IsPullback g' f' f g)
    (K : DerivedQCoh X) (K' : DerivedQCoh X')
    (α : (ModuleDerived.pullback g').obj ((inclusion X).obj K) ⟶ (inclusion X').obj K') :
    c.schemeHolds sq K K' α ↔
      ∀ (x' : c.schemeU') (i : ℤ),
        IsIso
          ((Scheme.DerivedQCoh.CohomologyBaseChangeModel.canonical
              c.fst c.snd c.mapU.left c.mapV'.left c.schemeIsPullback).pointMap
            (c.restrict K) (c.restrictK' sq K') (c.restrictMap sq K K' α) x' i) :=
  sorry

end EtaleBaseChangeChart

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
