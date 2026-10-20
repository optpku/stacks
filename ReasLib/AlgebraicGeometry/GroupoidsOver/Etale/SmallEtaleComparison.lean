/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.StructureSheafPresentation

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Hom
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ringed
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom
public import ReasLib.CategoryTheory.Fibered.InheritedTopology.Projection
public import ReasLib.CategoryTheory.Sites.MorphismOfSites
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous.SheafCompose
public import ReasLib.CategoryTheory.Sites.Topos.Continuous
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoids
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Topology

/-!
# Small étale comparison of a representing algebraic space

A bicategorical equivalence `e : F.toGroupoids ≌ X` induces a functor
`u : F_étale ⥤ X` by sending an étale morphism `φ : U ⟶ F` to `e.hom` applied
to the corresponding object of `S_F`.  Continuity and cocontinuity of `u` give
the morphism of ringed sites `π_F` and the morphism of ringed topoi `i_F`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open FiberedCategoryOver.Groupoids
open scoped Bicategory MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- The Yoneda component of an étale morphism `U ⟶ F`, as a section of the functor of
points of `F` over `U`. -/
def yonedaSection {F : AlgebraicSpace S} {U : Over S} (φ : AlgebraicSpace.ofOver U ⟶ F) :
    F.functorOfPoints.obj (op U) :=
  yonedaEquiv (φ : yoneda.obj U ⟶ F.functorOfPoints)

/-- `yonedaSection φ` is the Yoneda evaluation of `φ`. -/
theorem yonedaSection_eq {F : AlgebraicSpace S} {U : Over S}
    (φ : AlgebraicSpace.ofOver U ⟶ F) :
    yonedaSection φ = yonedaEquiv (φ : yoneda.obj U ⟶ F.functorOfPoints) :=
  rfl

/-- The object of `S_F` classified by an étale morphism `φ : U ⟶ F`. -/
def toGroupoidsObj {F : AlgebraicSpace S} (U : AlgebraicSpace.smallEtaleSite F) :
    F.toGroupoids.total :=
  op ⟨op U.left, yonedaSection U.hom⟩

/-- `toGroupoidsObj U` is the opposite category-of-elements object classified by `U.hom`. -/
theorem toGroupoidsObj_eq {F : AlgebraicSpace S} (U : AlgebraicSpace.smallEtaleSite F) :
    toGroupoidsObj U = op ⟨op U.left, yonedaSection U.hom⟩ :=
  rfl

/-- Compatibility of Yoneda components with a morphism of the small étale site. -/
theorem yonedaSection_map {F : AlgebraicSpace S}
    {U V : AlgebraicSpace.smallEtaleSite F} (f : U ⟶ V) :
    F.functorOfPoints.map f.left.op (yonedaSection V.hom) = yonedaSection U.hom :=
  sorry

/-- The morphism of `S_F` induced by a morphism of the small étale site of `F`. -/
def toGroupoidsMap {F : AlgebraicSpace S}
    {U V : AlgebraicSpace.smallEtaleSite F} (f : U ⟶ V) :
    toGroupoidsObj U ⟶ toGroupoidsObj V :=
  Quiver.Hom.op
    (CategoryOfElements.homMk
      ⟨op V.left, yonedaSection V.hom⟩
      ⟨op U.left, yonedaSection U.hom⟩
      f.left.op (yonedaSection_map f))

/-- The category-of-elements morphism associated to an identity is an identity. -/
theorem toGroupoidsMap_id {F : AlgebraicSpace S}
    (U : AlgebraicSpace.smallEtaleSite F) :
    toGroupoidsMap (𝟙 U) = 𝟙 (toGroupoidsObj U) :=
  sorry

/-- The category-of-elements morphism construction preserves composition. -/
theorem toGroupoidsMap_comp {F : AlgebraicSpace S}
    {U V W : AlgebraicSpace.smallEtaleSite F} (f : U ⟶ V) (g : V ⟶ W) :
    toGroupoidsMap (f ≫ g) = toGroupoidsMap f ≫ toGroupoidsMap g :=
  sorry

/-- The functor `F_étale ⥤ S_F` sending an étale morphism `φ : U ⟶ F` to the corresponding
object of the discrete Grothendieck construction. -/
def smallEtaleToGroupoids (F : AlgebraicSpace S) :
    AlgebraicSpace.smallEtaleSite F ⥤ F.toGroupoids.total where
  obj := toGroupoidsObj
  map := toGroupoidsMap
  map_id := toGroupoidsMap_id
  map_comp := toGroupoidsMap_comp

/-- The object map of `smallEtaleToGroupoids` is `toGroupoidsObj`. -/
theorem smallEtaleToGroupoids_obj (F : AlgebraicSpace S)
    (U : AlgebraicSpace.smallEtaleSite F) :
    (smallEtaleToGroupoids F).obj U = toGroupoidsObj U :=
  rfl

/-- The morphism map of `smallEtaleToGroupoids` is `toGroupoidsMap`. -/
theorem smallEtaleToGroupoids_map (F : AlgebraicSpace S)
    {U V : AlgebraicSpace.smallEtaleSite F} (f : U ⟶ V) :
    (smallEtaleToGroupoids F).map f = toGroupoidsMap f :=
  rfl

/-- The identity-equivalence specialization of `u` for `X = F.toGroupoids`. -/
def smallEtaleFunctor_id (G : AlgebraicSpace S) :
    AlgebraicSpace.smallEtaleSite G ⥤ G.toGroupoids.total :=
  smallEtaleToGroupoids G ⋙ toFunctor (𝟙 G.toGroupoids)

/-- The identity-equivalence specialization composes `smallEtaleToGroupoids` with the identity
`1`-morphism of `G.toGroupoids`. -/
theorem smallEtaleFunctor_id_eq (G : AlgebraicSpace S) :
    smallEtaleFunctor_id G = smallEtaleToGroupoids G ⋙ toFunctor (𝟙 G.toGroupoids) :=
  rfl

variable (F : AlgebraicSpace S) (X : GroupoidsOver S) (e : F.toGroupoids ≌ X)

/-- The functor `u : F_étale ⥤ X` induced by a representing equivalence
`e : F.toGroupoids ≌ X`. -/
def smallEtaleFunctor : AlgebraicSpace.smallEtaleSite F ⥤ X.total :=
  smallEtaleToGroupoids F ⋙ toFunctor e.hom

/-- An object of `F_étale` is sent to the image under `e.hom` of the object of `S_F`
classified by its structure morphism. -/
theorem smallEtaleFunctor_obj (U : AlgebraicSpace.smallEtaleSite F) :
    (smallEtaleFunctor F X e).obj U = (toFunctor e.hom).obj (toGroupoidsObj U) :=
  rfl

/-- Morphisms of `F_étale` are sent to the image under `e.hom` of the corresponding
morphism of `S_F`. -/
theorem smallEtaleFunctor_map {U V : AlgebraicSpace.smallEtaleSite F} (f : U ⟶ V) :
    (smallEtaleFunctor F X e).map f = (toFunctor e.hom).map (toGroupoidsMap f) :=
  rfl

/-- The functor `u` is continuous for the small étale topology of `F` and the associated
étale topology of `X`. -/
instance smallEtaleFunctor.instIsContinuous :
    (smallEtaleFunctor F X e).IsContinuous
      (AlgebraicSpace.smallEtaleTopology F) X.etaleTopology :=
  sorry

/-- The functor `u` is cocontinuous for the small étale topology of `F` and the associated
étale topology of `X`. -/
instance smallEtaleFunctor.instIsCocontinuous :
    (smallEtaleFunctor F X e).IsCocontinuous
      (AlgebraicSpace.smallEtaleTopology F) X.etaleTopology :=
  sorry

/-- A representing equivalence induces a continuous and cocontinuous functor
from the small étale site of an algebraic space to the associated étale site. -/
theorem smallEtaleFunctor_isContinuous_isCocontinuous :
    (smallEtaleFunctor F X e).IsContinuous
      (AlgebraicSpace.smallEtaleTopology F) X.etaleTopology ∧
    (smallEtaleFunctor F X e).IsCocontinuous
      (AlgebraicSpace.smallEtaleTopology F) X.etaleTopology :=
  ⟨inferInstance, inferInstance⟩

/-- The functor `u` is full, since `e` is an equivalence. -/
instance smallEtaleFunctor.instFull : (smallEtaleFunctor F X e).Full :=
  sorry

/-- The functor `u` is faithful, since `e` is an equivalence. -/
instance smallEtaleFunctor.instFaithful : (smallEtaleFunctor F X e).Faithful :=
  sorry

/-- The functor `u` is a morphism of étale sites `X_étale ⟶ F_étale`. -/
instance smallEtaleFunctor.instIsMorphismOfSites :
    IsMorphismOfSites (AlgebraicSpace.smallEtaleTopology F) X.etaleTopology
      (smallEtaleFunctor F X e) :=
  sorry

/-- Sheaf pullback along the small étale comparison functor preserves finite limits. -/
instance smallEtaleFunctor.sheafPullback_preservesFiniteLimits
    [HasWeakSheafify X.etaleTopology (Type u)]
    [∀ P : (AlgebraicSpace.smallEtaleSite F)ᵒᵖ ⥤ Type u,
        (smallEtaleFunctor F X e).op.HasLeftKanExtension P] :
    PreservesFiniteLimits
      ((smallEtaleFunctor F X e).sheafPullback (Type u)
        (AlgebraicSpace.smallEtaleTopology F) X.etaleTopology) :=
  sorry

/-- The tautological comparison sends each étale chart to an object over its domain. -/
theorem smallEtaleToGroupoids_p_obj (U : AlgebraicSpace.smallEtaleSite F) :
    (smallEtaleToGroupoids F ⋙ F.toGroupoids.p).obj U =
      (AlgebraicSpace.smallEtaleToOver F).obj U :=
  rfl

/-- Realization: `u` followed by the projection of `X` recovers the forgetful functor from
`F_étale` to `Over S`. -/
def smallEtaleFunctor_p :
    smallEtaleFunctor F X e ⋙ X.p ≅ AlgebraicSpace.smallEtaleToOver F :=
  Functor.isoWhiskerLeft (smallEtaleToGroupoids F) (eqToIso (comm e.hom)) ≪≫
    NatIso.ofComponents (fun U ↦ eqToIso (smallEtaleToGroupoids_p_obj F U))
      (by intro U V f; exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- Scheme-valued realization of `u`. -/
def smallEtaleFunctor_toScheme :
    smallEtaleFunctor F X e ⋙ X.p ⋙ Over.forget S ⟶
      AlgebraicSpace.smallEtaleToScheme F :=
  Functor.whiskerRight (smallEtaleFunctor_p F X e).hom (Over.forget S)

/-- Inverse scheme-valued realization of `u`. -/
def smallEtaleFunctor_toSchemeInv :
    AlgebraicSpace.smallEtaleToScheme F ⟶
      smallEtaleFunctor F X e ⋙ X.p ⋙ Over.forget S :=
  Functor.whiskerRight (smallEtaleFunctor_p F X e).inv (Over.forget S)

/-- The global-sections structure-sheaf map `O_F ⟶ u_* O_X` induced by realization. -/
def pi_structureSheafMap :
    (AlgebraicSpace.ringedSite F).structureSheaf ⟶
      ((smallEtaleFunctor F X e).sheafPushforwardContinuous RingCat.{u}
        (AlgebraicSpace.smallEtaleTopology F) X.etaleTopology).obj
        (etaleRingedSite X).structureSheaf :=
  Scheme.Site.structureSheafMap
      (AlgebraicSpace.smallEtaleTopology F) X.etaleTopology
      (AlgebraicSpace.smallEtaleToScheme F) (X.p ⋙ Over.forget S)
      (smallEtaleFunctor F X e) (smallEtaleFunctor_toScheme F X e)
      (AlgebraicSpace.structurePresheaf_isSheaf F)
      (etaleRingedSite_structurePresheaf_isSheaf X) ≫
    ((smallEtaleFunctor F X e).sheafPushforwardContinuous RingCat.{u}
        (AlgebraicSpace.smallEtaleTopology F) X.etaleTopology).map
      (structureSheafPresentationIso X).inv

/-- The morphism of ringed sites
`π_F : (X_étale, O_X) ⟶ (F_étale, O_F)` induced by `u`. -/
def pi : RingedSite.Hom (etaleRingedSite X) (AlgebraicSpace.ringedSite F) where
  base := smallEtaleFunctor F X e
  isMorphismOfSites := inferInstance
  structureSheafMap := pi_structureSheafMap F X e

/-- The base functor of `π_F` is `u`. -/
theorem pi_base :
    (pi F X e).base = smallEtaleFunctor F X e :=
  rfl

/-- Objectwise, the structure-sheaf map of `π_F` is pullback of global sections along
the realization morphism. -/
theorem pi_structureSheafMap_app (U : (AlgebraicSpace.smallEtaleSite F)ᵒᵖ) :
    (pi F X e).structureSheafMap.hom.app U =
      RingCat.ofHom ((smallEtaleFunctor_toScheme F X e).app U.unop).appTop.hom :=
  sorry

/-- Inverse-image comparison `u_p O_X ⟶ O_F` on global sections. -/
def inclusion_inverseStructureSheafMap :
    ((smallEtaleFunctor F X e).sheafPushforwardContinuous RingCat.{u}
        (AlgebraicSpace.smallEtaleTopology F) X.etaleTopology).obj
        (etaleRingedSite X).structureSheaf ⟶
      (AlgebraicSpace.ringedSite F).structureSheaf :=
  ((smallEtaleFunctor F X e).sheafPushforwardContinuous RingCat.{u}
        (AlgebraicSpace.smallEtaleTopology F) X.etaleTopology).map
      (structureSheafPresentationIso X).hom ≫
    Scheme.Site.inverseStructureSheafMap
      (AlgebraicSpace.smallEtaleTopology F) X.etaleTopology
      (AlgebraicSpace.smallEtaleToScheme F) (X.p ⋙ Over.forget S)
      (smallEtaleFunctor F X e) (smallEtaleFunctor_toSchemeInv F X e)
      (AlgebraicSpace.structurePresheaf_isSheaf F)
      (etaleRingedSite_structurePresheaf_isSheaf X)

variable [smallEtaleSheafify : HasSheafify (AlgebraicSpace.smallEtaleTopology F) (Type u)]
variable [smallEtaleTypeExtensions : ∀ P : (AlgebraicSpace.smallEtaleSite F)ᵒᵖ ⥤ Type u,
    (smallEtaleFunctor F X e).op.HasPointwiseRightKanExtension P]
variable [smallEtaleRingExtensions : ∀ P : (AlgebraicSpace.smallEtaleSite F)ᵒᵖ ⥤ RingCat.{u},
    (smallEtaleFunctor F X e).op.HasPointwiseRightKanExtension P]
variable [(AlgebraicSpace.smallEtaleTopology F).HasSheafCompose (forget RingCat.{u})]
variable [X.etaleTopology.HasSheafCompose (forget RingCat.{u})]
variable [smallEtaleForgetPreserves :
    (forget RingCat.{u}).PreservesRightKanExtensions (smallEtaleFunctor F X e).op]

/-- Continuous sheaf pushforward along `u` preserves finite limits. -/
instance smallEtaleFunctor.sheafPushforwardContinuous_preservesFiniteLimits :
    PreservesFiniteLimits
      ((smallEtaleFunctor F X e).sheafPushforwardContinuous (Type u)
        (AlgebraicSpace.smallEtaleTopology F) X.etaleTopology) :=
  sorry

/-- The morphism of topoi `i_F : Sh(F_étale) ⟶ Sh(X_étale)` presented by `u`, with inverse
image `u^p` and direct image the cocontinuous pushforward. -/
def inclusionToTopos :
    MorphismOfTopoiIn.{u + 1, u + 1, u, u, u}
      X.etaleTopology (AlgebraicSpace.smallEtaleTopology F) where
  inverseImageFunctor :=
    LeftExactFunctor.of
      ((smallEtaleFunctor F X e).sheafPushforwardContinuous (Type u)
        (AlgebraicSpace.smallEtaleTopology F) X.etaleTopology)
  pushforward :=
    (smallEtaleFunctor F X e).sheafPushforwardCocontinuous (Type u)
      (AlgebraicSpace.smallEtaleTopology F) X.etaleTopology
  adjunction :=
    (smallEtaleFunctor F X e).sheafAdjunctionCocontinuous (Type u)
      (AlgebraicSpace.smallEtaleTopology F) X.etaleTopology

/-- The inverse image of `inclusionToTopos` is continuous sheaf pushforward along `u`. -/
theorem inclusionToTopos_inverseImage :
    (inclusionToTopos F X e)⁻¹ =
      (smallEtaleFunctor F X e).sheafPushforwardContinuous (Type u)
        (AlgebraicSpace.smallEtaleTopology F) X.etaleTopology :=
  sorry

/-- The direct image of `inclusionToTopos` is cocontinuous sheaf pushforward along `u`. -/
theorem inclusionToTopos_pushforward :
    (inclusionToTopos F X e).pushforward =
      (smallEtaleFunctor F X e).sheafPushforwardCocontinuous (Type u)
        (AlgebraicSpace.smallEtaleTopology F) X.etaleTopology :=
  sorry

/-- Ring-valued cocontinuous direct image along `u`. -/
def inclusion_ringDirectImage :
    Sheaf (AlgebraicSpace.smallEtaleTopology F) RingCat.{u} ⥤
      Sheaf X.etaleTopology RingCat.{u} :=
  (smallEtaleFunctor F X e).sheafPushforwardCocontinuous RingCat.{u}
    (AlgebraicSpace.smallEtaleTopology F) X.etaleTopology

/-- Forgetting rings commutes with the cocontinuous direct image along `u`. -/
def inclusion_ringDirectImageForgetIso :
    inclusion_ringDirectImage F X e ⋙ sheafCompose X.etaleTopology (forget RingCat.{u}) ≅
      sheafCompose (AlgebraicSpace.smallEtaleTopology F) (forget RingCat.{u}) ⋙
        (inclusionToTopos F X e).pushforward :=
  Functor.sheafPushforwardCocontinuous.compSheafComposeIso
      (smallEtaleFunctor F X e) (forget RingCat.{u})
      (AlgebraicSpace.smallEtaleTopology F) X.etaleTopology

/-- Direct-image form of the structure-sheaf map of `i_F`. -/
def inclusion_directStructureMap :
    (etaleRingedSite X).structureSheaf ⟶
      (inclusion_ringDirectImage F X e).obj (AlgebraicSpace.ringedSite F).structureSheaf :=
  ((smallEtaleFunctor F X e).sheafAdjunctionCocontinuous RingCat.{u}
      (AlgebraicSpace.smallEtaleTopology F) X.etaleTopology).homEquiv _ _
    (inclusion_inverseStructureSheafMap F X e)

/-- The direct-image structure map of `i_F` preserves internal-ring operations. -/
theorem inclusion_directStructureMap_isRingCompatible :
    @RingedSite.ToposHom.Direct.IsRingCompatible
      (AlgebraicSpace.ringedSite F) (etaleRingedSite X) _ _
      (inclusionToTopos F X e) (inclusion_ringDirectImage F X e)
      (inclusion_ringDirectImageForgetIso F X e)
      (inclusion_directStructureMap F X e) :=
  sorry

/-- The morphism of ringed topoi
`i_F : (Sh(F_étale), O_F) ⟶ (Sh(X_étale), O_X)` induced by `u`. -/
def inclusion :
    RingedSite.ToposHom (AlgebraicSpace.ringedSite F) (etaleRingedSite X) :=
  @RingedSite.ToposHom.ofDirectImage
    (AlgebraicSpace.ringedSite F) (etaleRingedSite X) _ _
    (inclusionToTopos F X e) (inclusion_ringDirectImage F X e)
    (inclusion_ringDirectImageForgetIso F X e)
    (inclusion_directStructureMap F X e)
    (inclusion_directStructureMap_isRingCompatible F X e)

/-- The underlying topos morphism of `i_F` is `inclusionToTopos`. -/
theorem inclusion_toTopos :
    (inclusion F X e).toTopos = inclusionToTopos F X e :=
  sorry

/-- The inverse image of `i_F` is continuous sheaf pushforward along `u`. -/
theorem inclusion_inverseImage :
    (inclusion F X e).toTopos.inverseImage =
      (smallEtaleFunctor F X e).sheafPushforwardContinuous (Type u)
        (AlgebraicSpace.smallEtaleTopology F) X.etaleTopology :=
  sorry

/-- The direct image of `i_F` is cocontinuous sheaf pushforward along `u`. -/
theorem inclusion_pushforward :
    (inclusion F X e).toTopos.pushforward =
      (smallEtaleFunctor F X e).sheafPushforwardCocontinuous (Type u)
        (AlgebraicSpace.smallEtaleTopology F) X.etaleTopology :=
  sorry

variable [HasWeakSheafify X.etaleTopology (Type u)]
variable [∀ P : (AlgebraicSpace.smallEtaleSite F)ᵒᵖ ⥤ Type u,
    (smallEtaleFunctor F X e).op.HasLeftKanExtension P]

/-- The morphism of topoi presented by `π_F` as a continuous functor of sites. -/
def piToTopos :
    MorphismOfTopoiIn.{u + 1, u + 1, u, u, u}
      (AlgebraicSpace.smallEtaleTopology F) X.etaleTopology :=
  (smallEtaleFunctor F X e).morphismOfTopoiInOfContinuous
    (AlgebraicSpace.smallEtaleTopology F) X.etaleTopology

omit smallEtaleSheafify smallEtaleTypeExtensions smallEtaleRingExtensions
  smallEtaleForgetPreserves in
/-- Forgetting rings commutes with continuous sheaf pushforward along `u`.
The underlying presheaf comparison is the definitional whiskering identity
(`sheafPushforwardContinuousCompSheafToPresheafIso` is `Iso.refl`, and `forget`
commutes with `u.op` on presheaves); this iso descends that identity along
`fullyFaithfulSheafToPresheaf`. -/
def piToposHomForgetIso :
    (smallEtaleFunctor F X e).sheafPushforwardContinuous RingCat.{u}
          (AlgebraicSpace.smallEtaleTopology F) X.etaleTopology ⋙
        sheafCompose (AlgebraicSpace.smallEtaleTopology F) (forget RingCat.{u}) ≅
      sheafCompose X.etaleTopology (forget RingCat.{u}) ⋙
        (piToTopos F X e).pushforward :=
  Functor.fullyFaithfulCancelRight
    (sheafToPresheaf (AlgebraicSpace.smallEtaleTopology F) (Type u))
    (NatIso.ofComponents (fun _ ↦ Iso.refl _)
      (by intro A B f; exact (Category.comp_id _).trans (Category.id_comp _).symm))

omit smallEtaleSheafify smallEtaleTypeExtensions smallEtaleRingExtensions
  smallEtaleForgetPreserves in
/-- The direct-image structure map of `π_F` preserves internal-ring operations. -/
theorem piToposHom_isRingCompatible :
    @RingedSite.ToposHom.Direct.IsRingCompatible
      (etaleRingedSite X) (AlgebraicSpace.ringedSite F) _ _
      (piToTopos F X e)
      ((smallEtaleFunctor F X e).sheafPushforwardContinuous RingCat.{u}
        (AlgebraicSpace.smallEtaleTopology F) X.etaleTopology)
      (piToposHomForgetIso F X e) (pi F X e).structureSheafMap :=
  sorry

omit smallEtaleSheafify smallEtaleTypeExtensions smallEtaleRingExtensions
  smallEtaleForgetPreserves in
/-- The morphism of ringed topoi presented by `π_F`. -/
def piToposHom :
    RingedSite.ToposHom (etaleRingedSite X) (AlgebraicSpace.ringedSite F) :=
  @RingedSite.ToposHom.ofDirectImage
    (etaleRingedSite X) (AlgebraicSpace.ringedSite F) _ _
    (piToTopos F X e)
    ((smallEtaleFunctor F X e).sheafPushforwardContinuous RingCat.{u}
      (AlgebraicSpace.smallEtaleTopology F) X.etaleTopology)
    (piToposHomForgetIso F X e) (pi F X e).structureSheafMap
    (piToposHom_isRingCompatible F X e)

omit smallEtaleSheafify smallEtaleTypeExtensions smallEtaleRingExtensions
  smallEtaleForgetPreserves in
/-- The underlying topos morphism of the ringed morphism `π_F` is `piToTopos`. -/
theorem piToposHom_toTopos :
    (piToposHom F X e).toTopos = piToTopos F X e :=
  sorry

/-- The composite comparison on the ringed topos of the small étale site admits
an invertible inverse-image comparison with the identity, compatible with structure maps. -/
theorem pi_comp_inclusion :
    ∃ α : (RingedSite.ToposHom.comp (inclusion F X e) (piToposHom F X e)).toTopos.inverseImage ≅
        (RingedSite.ToposHom.id (AlgebraicSpace.ringedSite F)).toTopos.inverseImage,
      (RingedSite.ToposHom.comp (inclusion F X e) (piToposHom F X e)).structureMap =
        (MorphismOfTopoiIn.ringInverseImageNatIso α).hom.app
            (AlgebraicSpace.ringedSite F).structureSheaf ≫
          (RingedSite.ToposHom.id (AlgebraicSpace.ringedSite F)).structureMap :=
  sorry

/-- The composite comparison has inverse image naturally isomorphic to that
of the identity on the small étale topos. -/
theorem piToTopos_comp_inclusionToTopos :
    Nonempty ((MorphismOfTopoiIn.comp (piToTopos F X e)
        (inclusionToTopos F X e)).inverseImage ≅
      (MorphismOfTopoiIn.id (AlgebraicSpace.smallEtaleTopology F) :
        MorphismOfTopoiIn.{u + 1, u + 1, u, u, u}
          (AlgebraicSpace.smallEtaleTopology F)
          (AlgebraicSpace.smallEtaleTopology F)).inverseImage) :=
  sorry

/-- The direct image of `π_F` equals the inverse image of `i_F`. -/
theorem pi_pushforward_eq_inclusion_inverseImage :
    (piToposHom F X e).toTopos.pushforward =
      (inclusion F X e).toTopos.inverseImage :=
  sorry

variable [HasSheafify (AlgebraicSpace.smallEtaleTopology F) (Type (u + 1))]
variable [∀ P : (AlgebraicSpace.smallEtaleSite F)ᵒᵖ ⥤ Type (u + 1),
    (smallEtaleFunctor F X e).op.HasPointwiseRightKanExtension P]
variable [∀ P : (AlgebraicSpace.smallEtaleSite F)ᵒᵖ ⥤ Type (u + 1),
    (smallEtaleFunctor F X e).op.HasLeftKanExtension P]
variable [HasWeakSheafify X.etaleTopology (Type (u + 1))]

/-- Set-valued sheaf pullback along `u` preserves finite limits. -/
instance smallEtaleFunctor.sheafPullback_type_preservesFiniteLimits :
    PreservesFiniteLimits
      ((smallEtaleFunctor F X e).sheafPullback (Type (u + 1))
        (AlgebraicSpace.smallEtaleTopology F) X.etaleTopology) :=
  sorry

/-- Set-valued form of `π_{F,*} = i_F⁻¹` on sheaves of types in universe `u+1`. -/
theorem pi_pushforward_eq_inclusion_inverseImage_type :
    ((smallEtaleFunctor F X e).morphismOfTopoiInOfContinuous
          (AlgebraicSpace.smallEtaleTopology F) X.etaleTopology).pushforward =
      (smallEtaleFunctor F X e).sheafPushforwardContinuous (Type (u + 1))
        (AlgebraicSpace.smallEtaleTopology F) X.etaleTopology :=
  sorry

end AlgebraicGeometry.GroupoidsOver
