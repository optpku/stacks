/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Limits.HasLimits
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.ModuleAdjunction
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Pseudofunctor
public import ReasLib.CategoryTheory.Fibered.Groupoids.UnderlyingFunctorIso
public import ReasLib.CategoryTheory.Fibered.InheritedTopology.Morphism
public import ReasLib.CategoryTheory.Sites.Topos.Composition
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous.SheafCompose
public import ReasLib.CategoryTheory.Sites.Topos.InternalModule
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap94.«94_8_2_1_FullyFaithful»
public import stacks_project.Chap96.Lemma_96_8_1_Comparison
public import stacks_project.Chap96.«96_10_3_1_Comparison»
public import stacks_project.Chap96.«96_10_3_3_Restriction»

/-!
# Algebraic-space comparison morphisms of étale modules

A 2-commutative triangle of 1-morphisms of categories fibred in groupoids, with
`𝒰` and `𝒱` represented by algebraic spaces `U` and `V`, induces a comparison
morphism `c_φ : a_small^*(g^* F |_{V_étale}) ⟶ f^* F |_{U_étale}` of
`𝒪_{U_étale}`-modules.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Functor Opposite
open FiberedCategoryOver.Groupoids
open RingedSite.Hom
open CategoryTheory.Limits
open CategoryTheory.Sheaf.InternalModule
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- The total functor of a 1-morphism is a morphism of associated étale sites. -/
instance toFunctor_isMorphismOfSites_etale {X Y : GroupoidsOver S} (h : X ⟶ Y) :
    IsMorphismOfSites X.etaleTopology Y.etaleTopology (toFunctor h) :=
  sorry

/-- The total functor of a 1-morphism is continuous for associated étale topologies. -/
instance toFunctor_isContinuous_etale {X Y : GroupoidsOver S} (h : X ⟶ Y) :
    (toFunctor h).IsContinuous X.etaleTopology Y.etaleTopology :=
  (toFunctor_isMorphismOfSites_etale h).toIsContinuous

/-- The composite `toFunctor h ⋙ Y.p` is continuous from `X_étale` to the big
étale site of `S`. -/
instance toFunctor_comp_p_isContinuous_etale {X Y : GroupoidsOver S} (h : X ⟶ Y) :
    (toFunctor h ⋙ Y.p).IsContinuous X.etaleTopology
      (StandardTopology.etale.overTopology S) :=
  toFunctor_comp_p_isContinuous h StandardTopology.etale

/-- A composite of total functors is continuous for associated étale topologies. -/
instance toFunctor_comp_isContinuous_etale {X Y Z : GroupoidsOver S}
    (h : X ⟶ Y) (k : Y ⟶ Z) :
    (toFunctor h ⋙ toFunctor k).IsContinuous X.etaleTopology Z.etaleTopology :=
  Functor.isContinuous_comp (toFunctor h) (toFunctor k)
    X.etaleTopology Y.etaleTopology Z.etaleTopology

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

/-- Pointwise right Kan extensions exist for ring-valued presheaves along a cartesian
total functor. -/
instance toCartesian_op_hasPointwiseRightKanExtension_ring {X Y : GroupoidsOver S}
    (h : X ⟶ Y) (P : X.totalᵒᵖ ⥤ RingCat.{u}) :
    (toCartesianBasedFunctor h).toFunctor.op.HasPointwiseRightKanExtension P :=
  sorry

/-- Forgetting rings preserves the right Kan extensions used to form cocontinuous
direct image along a cartesian total functor. -/
instance forget_preservesRightKanExtensions_toCartesian {X Y : GroupoidsOver S}
    (h : X ⟶ Y) :
    (forget RingCat.{u}).PreservesRightKanExtensions
      (toCartesianBasedFunctor h).toFunctor.op :=
  sorry

/-- The cartesian total functor is continuous for associated étale topologies. -/
instance toCartesianBasedFunctor_isContinuous_etale {X Y : GroupoidsOver S}
    (h : X ⟶ Y) :
    (toCartesianBasedFunctor h).toFunctor.IsContinuous
      X.etaleTopology Y.etaleTopology :=
  CartesianBasedFunctor.inheritedTopology.isContinuous
    (toCartesianBasedFunctor h) (StandardTopology.etale.overTopology S)

/-- The cartesian total functor is cocontinuous for associated étale topologies. -/
instance toCartesianBasedFunctor_isCocontinuous_etale {X Y : GroupoidsOver S}
    (h : X ⟶ Y) :
    (toCartesianBasedFunctor h).toFunctor.IsCocontinuous
      X.etaleTopology Y.etaleTopology :=
  CartesianBasedFunctor.inheritedTopology.isCocontinuous
    (toCartesianBasedFunctor h) (StandardTopology.etale.overTopology S)

/-- The cartesian total functor agrees with `toFunctor`. -/
theorem cartesian_toFunctor_eq {X Y : GroupoidsOver S} (h : X ⟶ Y) :
    (toCartesianBasedFunctor h).toFunctor = toFunctor h :=
  congrArg (fun F => F.toFunctor) (toCartesianBasedFunctor.toBasedFunctor h)

/-- The structure-sheaf map of `etaleSiteHom`, identifying `𝒪_X` with the
continuous pushforward of `𝒪_Y` along `toFunctor h`. -/
def etaleSiteHom_structureSheafMap {X Y : GroupoidsOver S} (h : X ⟶ Y) :
    (etaleRingedSite X).structureSheaf ⟶
      ((toFunctor h).sheafPushforwardContinuous RingCat.{u}
        X.etaleTopology Y.etaleTopology).obj (etaleRingedSite Y).structureSheaf :=
  (sheafPushforwardContinuousIso (eqToIso (comm h).symm) RingCat.{u}
      X.etaleTopology (StandardTopology.etale.overTopology S)).hom.app
    (StandardTopology.Big.structureSheaf StandardTopology.etale S)

/-- The morphism of étale ringed sites induced by a 1-morphism of categories
fibred in groupoids, with underlying functor `toFunctor h`. -/
def etaleSiteHom {X Y : GroupoidsOver S} (h : X ⟶ Y) :
    RingedSite.Hom (etaleRingedSite Y) (etaleRingedSite X) where
  base := toFunctor h
  isMorphismOfSites := toFunctor_isMorphismOfSites_etale h
  structureSheafMap := etaleSiteHom_structureSheafMap h

/-- Inverse image `h^* = h⁻¹` of étale `𝒪`-modules along a 1-morphism of
categories fibred in groupoids. -/
def etaleModuleInverseImage {X Y : GroupoidsOver S} (h : X ⟶ Y) :
    SheafOfModules.{u} (etaleRingedSite Y).structureSheaf ⥤
      SheafOfModules.{u} (etaleRingedSite X).structureSheaf :=
  (etaleSiteHom h).modulePushforward.{u}

/-- `etaleModuleInverseImage h` is module pushforward along `etaleSiteHom h`. -/
theorem etaleModuleInverseImage_eq {X Y : GroupoidsOver S} (h : X ⟶ Y) :
    etaleModuleInverseImage h = (etaleSiteHom h).modulePushforward.{u} :=
  rfl

/-- Inverse-image form of the structure-sheaf map of a 1-morphism, identifying
`h⁻¹ 𝒪_Y` with `𝒪_X`. -/
def etaleModuleStructureSheafInv {X Y : GroupoidsOver S} (h : X ⟶ Y) :
    ((toFunctor h).sheafPushforwardContinuous RingCat.{u}
        X.etaleTopology Y.etaleTopology).obj (etaleRingedSite Y).structureSheaf ⟶
      (etaleRingedSite X).structureSheaf :=
  (sheafPushforwardContinuousIso (eqToIso (comm h).symm) RingCat.{u}
      X.etaleTopology (StandardTopology.etale.overTopology S)).inv.app
    (StandardTopology.Big.structureSheaf StandardTopology.etale S)

/-- Direct-image form of the structure-sheaf map of a 1-morphism. -/
def etaleModuleStructureSheafMap {X Y : GroupoidsOver S} (h : X ⟶ Y) :
    (etaleRingedSite Y).structureSheaf ⟶
      ((toCartesianBasedFunctor h).toFunctor.sheafPushforwardCocontinuous
          RingCat.{u} X.etaleTopology Y.etaleTopology).obj
        (etaleRingedSite X).structureSheaf :=
  ((toCartesianBasedFunctor h).toFunctor.sheafAdjunctionCocontinuous
      RingCat.{u} X.etaleTopology Y.etaleTopology).homEquiv _ _
    (etaleModuleStructureSheafInv h)

/-- The direct-image structure map of a 1-morphism preserves internal-ring operations. -/
theorem etaleModuleStructureSheafMap_isRingCompatible {X Y : GroupoidsOver S}
    (h : X ⟶ Y) :
    @RingedSite.ToposHom.Direct.IsRingCompatible
      (etaleRingedSite X) (etaleRingedSite Y) inferInstance inferInstance
      ((toCartesianBasedFunctor h).morphismOfTopoiIn
        (StandardTopology.etale.overTopology S) :
        MorphismOfTopoiIn.{u + 1, u + 1, u, u, u} Y.etaleTopology X.etaleTopology)
      ((toCartesianBasedFunctor h).toFunctor.sheafPushforwardCocontinuous
        RingCat.{u} X.etaleTopology Y.etaleTopology)
      (Functor.sheafPushforwardCocontinuous.compSheafComposeIso
        (toCartesianBasedFunctor h).toFunctor (forget RingCat.{u})
        X.etaleTopology Y.etaleTopology)
      (etaleModuleStructureSheafMap h) :=
  sorry

/-- The morphism of étale ringed topoi induced by a 1-morphism of categories
fibred in groupoids. -/
def etaleRingedToposHom {X Y : GroupoidsOver S} (h : X ⟶ Y) :
    RingedSite.ToposHom (etaleRingedSite X) (etaleRingedSite Y) :=
  @RingedSite.ToposHom.ofDirectImage (etaleRingedSite X) (etaleRingedSite Y)
    inferInstance inferInstance
    ((toCartesianBasedFunctor h).morphismOfTopoiIn
      (StandardTopology.etale.overTopology S) :
      MorphismOfTopoiIn.{u + 1, u + 1, u, u, u} Y.etaleTopology X.etaleTopology)
    ((toCartesianBasedFunctor h).toFunctor.sheafPushforwardCocontinuous
      RingCat.{u} X.etaleTopology Y.etaleTopology)
    (Functor.sheafPushforwardCocontinuous.compSheafComposeIso
      (toCartesianBasedFunctor h).toFunctor (forget RingCat.{u})
      X.etaleTopology Y.etaleTopology)
    (etaleModuleStructureSheafMap h)
    (etaleModuleStructureSheafMap_isRingCompatible h)

/-- Restriction of scalars along the inverse-image structure map of a 1-morphism
is a right adjoint. -/
instance etaleRingedToposHom_restrictScalars_isRightAdjoint {X Y : GroupoidsOver S}
    (h : X ⟶ Y) :
    (SheafOfModules.restrictScalars.{u}
      (etaleRingedToposHom h).structureMap).IsRightAdjoint :=
  sorry

/-- Direct image `h_*` of étale `𝒪`-modules along a 1-morphism. -/
def etaleModuleDirectImage {X Y : GroupoidsOver S} (h : X ⟶ Y) :
    SheafOfModules.{u} (etaleRingedSite X).structureSheaf ⥤
      SheafOfModules.{u} (etaleRingedSite Y).structureSheaf :=
  (etaleRingedToposHom h).modulePushforward

/-- `etaleModuleDirectImage` is the module direct image of `etaleRingedToposHom`. -/
theorem etaleModuleDirectImage_eq {X Y : GroupoidsOver S} (h : X ⟶ Y) :
    etaleModuleDirectImage h = (etaleRingedToposHom h).modulePushforward :=
  rfl

/-- Unit of `h^* ⊣ h_*` on étale modules, for the topos-level inverse image. -/
def etaleModuleUnit {X Y : GroupoidsOver S} (h : X ⟶ Y)
    (G : SheafOfModules.{u} (etaleRingedSite Y).structureSheaf) :
    G ⟶ (etaleModuleDirectImage h).obj ((etaleRingedToposHom h).modulePullback.obj G) :=
  (etaleRingedToposHom h).moduleAdjunction.unit.app G

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
of the inverse images, via `pushforwardComp` and the real total-functor
composition isomorphism. -/
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
inverse images, via the underlying total-functor isomorphism `toFunctorIso`. -/
def etaleModuleInverseImage_iso {X Y : GroupoidsOver S} {h₁ h₂ : X ⟶ Y} (e : h₁ ≅ h₂) :
    etaleModuleInverseImage h₁ ≅ etaleModuleInverseImage h₂ :=
  (etaleModuleInverseImage_iso₀ e ≪≫ etaleModuleInverseImage_iso₁ e).symm

/-- The morphism of algebraic spaces corresponding to a presented 1-morphism `a`. -/
def moduleComparisonSpaceMorphism {Ucfg Vcfg : GroupoidsOver S} (a : Ucfg ⟶ Vcfg)
    {U V : AlgebraicSpace S} (eU : U.toGroupoids ≌ Ucfg) (eV : V.toGroupoids ≌ Vcfg) :
    U ⟶ V :=
  AlgebraicSpace.toGroupoids.recover eU.symm eV.symm a

/-- 2-cell transport `a^* g^* ≅ f^*` on étale modules. -/
def etaleModuleInverseImage_twoCell {X Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) (f : Ucfg ⟶ X) (g : Vcfg ⟶ X) (φ : a ≫ g ≅ f) :
    etaleModuleInverseImage g ⋙ etaleModuleInverseImage a ≅
      etaleModuleInverseImage f :=
  etaleModuleInverseImage_comp a g ≪≫ etaleModuleInverseImage_iso φ

/-- Underlying type-valued comparison from geometric inverse image of `G` to
continuous pushforward of `G` along `toFunctor h`. -/
def etaleModuleInverseImage_fromPullbackUnderlying {X Y : GroupoidsOver S}
    (h : X ⟶ Y) (G : SheafOfModules.{u} (etaleRingedSite Y).structureSheaf) :
    (ToInternal.underlying
          ((etaleRingedToposHom h).toTopos.ringInverseImage.obj
            (etaleRingedSite Y).structureSheaf)).obj
        (((etaleRingedToposHom h).toTopos.moduleInverseImage
            (etaleRingedSite Y).structureSheaf).obj G) ⟶
      (ToInternal.underlying
          ((etaleRingedToposHom h).toTopos.ringInverseImage.obj
            (etaleRingedSite Y).structureSheaf)).obj
        ((SheafOfModules.restrictScalars (etaleRingedToposHom h).structureMap).obj
          ((etaleModuleInverseImage h).obj G)) :=
  ((etaleRingedToposHom h).toTopos.moduleInverseImageForgetIso
        (etaleRingedSite Y).structureSheaf).hom.app G ≫
    (asIso
        (CartesianBasedFunctor.morphismOfTopoiIn.inverseImageComparison
          (toCartesianBasedFunctor h)
          (StandardTopology.etale.overTopology S))).hom.app
      ((ToInternal.underlying (etaleRingedSite Y).structureSheaf).obj G) ≫
      (sheafPushforwardContinuousIso (eqToIso (cartesian_toFunctor_eq h))
          (Type u) X.etaleTopology Y.etaleTopology).hom.app
        ((ToInternal.underlying (etaleRingedSite Y).structureSheaf).obj G)

/-- Geometric inverse image of `G` over `h⁻¹ 𝒪_Y`, compared with restriction of
scalars of the site-level inverse image. -/
def etaleModuleInverseImage_fromPullback {X Y : GroupoidsOver S} (h : X ⟶ Y)
    (G : SheafOfModules.{u} (etaleRingedSite Y).structureSheaf) :
    ((etaleRingedToposHom h).toTopos.moduleInverseImage
        (etaleRingedSite Y).structureSheaf).obj G ⟶
      (SheafOfModules.restrictScalars (etaleRingedToposHom h).structureMap).obj
        ((etaleModuleInverseImage h).obj G) :=
  homOfUnderlying
    ((etaleRingedToposHom h).toTopos.ringInverseImage.obj
      (etaleRingedSite Y).structureSheaf)
    (etaleModuleInverseImage_fromPullbackUnderlying h G) sorry sorry

/-- Topos-level module pullback compared with site-level inverse image `h^*`. -/
def etaleModulePullbackToInverseImage {X Y : GroupoidsOver S} (h : X ⟶ Y)
    (G : SheafOfModules.{u} (etaleRingedSite Y).structureSheaf) :
    (etaleRingedToposHom h).modulePullback.obj G ⟶ (etaleModuleInverseImage h).obj G :=
  (RingedSite.ToposHom.ModulePullback.scalarHomEquiv (etaleRingedToposHom h)
      (((etaleRingedToposHom h).toTopos.moduleInverseImage
          (etaleRingedSite Y).structureSheaf).obj G)
      ((etaleModuleInverseImage h).obj G)).symm
    (etaleModuleInverseImage_fromPullback h G)

/-- Evaluation of a restricted CFG module at `W` recovers sections at `u_V(W)`. -/
def restrictDirectImageComparison_leftEval {Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) {V : AlgebraicSpace S} (eV : V.toGroupoids ≌ Vcfg)
    (H : SheafOfModules.{u} (etaleRingedSite Ucfg).structureSheaf)
    (W : AlgebraicSpace.smallEtaleSite V) :
    ((ToInternal.underlying (AlgebraicSpace.structureSheaf V)).obj
        ((restrictModules eV).obj ((etaleModuleDirectImage a).obj H))).obj.obj (op W) ≅
      ((ToInternal.underlying (etaleRingedSite Vcfg).structureSheaf).obj
        ((etaleModuleDirectImage a).obj H)).obj.obj
          (op ((smallEtaleFunctor V Vcfg eV).obj W)) :=
  Iso.refl _

/-- The comma category computing CFG pushforward at `u_V(W)`. -/
abbrev restrictDirectImageComparison_bigIndex {Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) {V : AlgebraicSpace S} (eV : V.toGroupoids ≌ Vcfg)
    (W : AlgebraicSpace.smallEtaleSite V) :=
  StructuredArrow (op ((smallEtaleFunctor V Vcfg eV).obj W))
    (toCartesianBasedFunctor a).toFunctor.op

/-- The comma category computing small étale pushforward at `W ×_V U`. -/
abbrev restrictDirectImageComparison_smallIndex {Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) {U V : AlgebraicSpace S}
    (eU : U.toGroupoids ≌ Ucfg) (eV : V.toGroupoids ≌ Vcfg)
    (W : AlgebraicSpace.smallEtaleSite V) :=
  AlgebraicSpace.compareSmallIndex (moduleComparisonSpaceMorphism a eU eV) W

/-- Kan diagram for CFG pushforward of the underlying sheaf at `u_V(W)`. -/
abbrev restrictDirectImageComparison_bigDiag {Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) {V : AlgebraicSpace S} (eV : V.toGroupoids ≌ Vcfg)
    (H : SheafOfModules.{u} (etaleRingedSite Ucfg).structureSheaf)
    (W : AlgebraicSpace.smallEtaleSite V) :
    restrictDirectImageComparison_bigIndex a eV W ⥤ Type u :=
  StructuredArrow.proj (op ((smallEtaleFunctor V Vcfg eV).obj W))
      (toCartesianBasedFunctor a).toFunctor.op ⋙
    ((ToInternal.underlying (etaleRingedSite Ucfg).structureSheaf).obj H).obj

/-- Kan diagram for small étale pushforward of the restricted underlying sheaf. -/
abbrev restrictDirectImageComparison_smallDiag {Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) {U V : AlgebraicSpace S}
    (eU : U.toGroupoids ≌ Ucfg) (eV : V.toGroupoids ≌ Vcfg)
    (H : SheafOfModules.{u} (etaleRingedSite Ucfg).structureSheaf)
    (W : AlgebraicSpace.smallEtaleSite V) :
    restrictDirectImageComparison_smallIndex a eU eV W ⥤ Type u :=
  StructuredArrow.proj
      (op ((AlgebraicSpace.etaleBaseChange
          (moduleComparisonSpaceMorphism a eU eV)).obj W))
      (AlgebraicSpace.smallEtaleInclusion U).op ⋙
    ((ToInternal.underlying (AlgebraicSpace.structureSheaf U)).obj
      ((restrictModules eU).obj H)).obj

/-- The inducing `2`-cell `eU.hom ≫ a ≅ map a_space ≫ eV.hom` of the recovered
morphism of algebraic spaces. -/
def restrictDirectImageComparison_presentedTwoCell {Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) {U V : AlgebraicSpace S}
    (eU : U.toGroupoids ≌ Ucfg) (eV : V.toGroupoids ≌ Vcfg) :
    eU.hom ≫ a ≅
      AlgebraicSpace.toGroupoids.map (moduleComparisonSpaceMorphism a eU eV) ≫ eV.hom :=
  let α := Classical.choice
      (AlgebraicSpace.toGroupoids.InducesHom.recover eU.symm eV.symm a)
  let a_space := moduleComparisonSpaceMorphism a eU eV
  (ρ_ (eU.hom ≫ a)).symm ≪≫
    Bicategory.whiskerLeftIso (eU.hom ≫ a) eV.counit.symm ≪≫
    (α_ (eU.hom ≫ a) eV.inv eV.hom).symm ≪≫
    Bicategory.whiskerRightIso (α_ eU.hom a eV.inv) eV.hom ≪≫
    Bicategory.whiskerRightIso (Bicategory.whiskerLeftIso eU.hom α) eV.hom ≪≫
    Bicategory.whiskerRightIso
      (α_ eU.hom eU.inv (AlgebraicSpace.toGroupoids.map a_space)).symm eV.hom ≪≫
    (α_ (eU.hom ≫ eU.inv) (AlgebraicSpace.toGroupoids.map a_space) eV.hom) ≪≫
    Bicategory.whiskerRightIso eU.unit.symm
      (AlgebraicSpace.toGroupoids.map a_space ≫ eV.hom) ≪≫
    λ_ (AlgebraicSpace.toGroupoids.map a_space ≫ eV.hom)

/-- The morphism `a(u_U(T')) ⟶ u_V(W)` in `Vcfg`, obtained by transporting the
identity-presentation comparison morphism of `96.10.3.1` along `eV`. -/
def restrictDirectImageComparison_indexHom {Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) {U V : AlgebraicSpace S}
    (eU : U.toGroupoids ≌ Ucfg) (eV : V.toGroupoids ≌ Vcfg)
    (W : AlgebraicSpace.smallEtaleSite V)
    (k : restrictDirectImageComparison_smallIndex a eU eV W) :
    (toCartesianBasedFunctor a).toFunctor.obj
        ((smallEtaleFunctor U Ucfg eU).obj k.right.unop) ⟶
      (smallEtaleFunctor V Vcfg eV).obj W :=
  let x := (smallEtaleToGroupoids U).obj k.right.unop
  let a_space := moduleComparisonSpaceMorphism a eU eV
  (eqToIso (cartesian_toFunctor_eq a)).hom.app ((toFunctor eU.hom).obj x) ≫
    (ObjectProperty.FullSubbicategory.toFunctor.compIso eU.hom a).hom.app x ≫
      (toFunctorIso (restrictDirectImageComparison_presentedTwoCell a eU eV)).hom.app x ≫
        (ObjectProperty.FullSubbicategory.toFunctor.compIso
            (AlgebraicSpace.toGroupoids.map a_space) eV.hom).inv.app x ≫
          (toFunctor eV.hom).map
            ((eqToIso (cartesian_toFunctor_eq (AlgebraicSpace.toGroupoids.map a_space)).symm).hom.app x ≫
              AlgebraicSpace.compareIndexHom a_space k)

/-- Opposite form of `restrictDirectImageComparison_indexHom`, as a structured arrow. -/
def restrictDirectImageComparison_indexArrow {Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) {U V : AlgebraicSpace S}
    (eU : U.toGroupoids ≌ Ucfg) (eV : V.toGroupoids ≌ Vcfg)
    (W : AlgebraicSpace.smallEtaleSite V)
    (k : restrictDirectImageComparison_smallIndex a eU eV W) :
    op ((smallEtaleFunctor V Vcfg eV).obj W) ⟶
      (toCartesianBasedFunctor a).toFunctor.op.obj
        (op ((smallEtaleFunctor U Ucfg eU).obj k.right.unop)) :=
  (restrictDirectImageComparison_indexHom a eU eV W k).op

/-- Functor from the small-étale Kan comma category to the CFG Kan comma category. -/
def restrictDirectImageComparison_indexMap {Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) {U V : AlgebraicSpace S}
    (eU : U.toGroupoids ≌ Ucfg) (eV : V.toGroupoids ≌ Vcfg)
    (W : AlgebraicSpace.smallEtaleSite V) :
    restrictDirectImageComparison_smallIndex a eU eV W ⥤
      restrictDirectImageComparison_bigIndex a eV W where
  obj k := StructuredArrow.mk (restrictDirectImageComparison_indexArrow a eU eV W k)
  map {k k'} α :=
    StructuredArrow.homMk ((smallEtaleFunctor U Ucfg eU).map α.right.unop).op sorry
  map_id _ := sorry
  map_comp _ _ := sorry

/-- The Kan diagrams agree after restriction along `restrictDirectImageComparison_indexMap`. -/
def restrictDirectImageComparison_diagIso {Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) {U V : AlgebraicSpace S}
    (eU : U.toGroupoids ≌ Ucfg) (eV : V.toGroupoids ≌ Vcfg)
    (H : SheafOfModules.{u} (etaleRingedSite Ucfg).structureSheaf)
    (W : AlgebraicSpace.smallEtaleSite V) :
    restrictDirectImageComparison_indexMap a eU eV W ⋙
        restrictDirectImageComparison_bigDiag a eV H W ≅
      restrictDirectImageComparison_smallDiag a eU eV H W :=
  NatIso.ofComponents (fun _ => Iso.refl _) sorry

/-- Type-valued limits exist for the CFG Kan diagram at `u_V(W)`. -/
instance restrictDirectImageComparison_bigDiag_hasLimit {Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) {V : AlgebraicSpace S} (eV : V.toGroupoids ≌ Vcfg)
    (H : SheafOfModules.{u} (etaleRingedSite Ucfg).structureSheaf)
    (W : AlgebraicSpace.smallEtaleSite V) :
    HasLimit (restrictDirectImageComparison_bigDiag a eV H W) :=
  sorry

/-- Type-valued limits exist for the small-étale Kan diagram at `W ×_V U`. -/
instance restrictDirectImageComparison_smallDiag_hasLimit {Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) {U V : AlgebraicSpace S}
    (eU : U.toGroupoids ≌ Ucfg) (eV : V.toGroupoids ≌ Vcfg)
    (H : SheafOfModules.{u} (etaleRingedSite Ucfg).structureSheaf)
    (W : AlgebraicSpace.smallEtaleSite V) :
    HasLimit (restrictDirectImageComparison_smallDiag a eU eV H W) :=
  AlgebraicSpace.EtaleTopos.allChartHasLimit U
    ((ToInternal.underlying (AlgebraicSpace.structureSheaf U)).obj ((restrictModules eU).obj H))
    ((AlgebraicSpace.etaleBaseChange (moduleComparisonSpaceMorphism a eU eV)).obj W)

/-- Type-valued limits exist after restriction along the index functor. -/
instance restrictDirectImageComparison_indexBigDiag_hasLimit {Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) {U V : AlgebraicSpace S}
    (eU : U.toGroupoids ≌ Ucfg) (eV : V.toGroupoids ≌ Vcfg)
    (H : SheafOfModules.{u} (etaleRingedSite Ucfg).structureSheaf)
    (W : AlgebraicSpace.smallEtaleSite V) :
    HasLimit
      (restrictDirectImageComparison_indexMap a eU eV W ⋙
        restrictDirectImageComparison_bigDiag a eV H W) :=
  sorry

/-- Restriction of compatible families from the CFG Kan comma category to the
small-étale Kan comma category. -/
def restrictDirectImageComparison_limitHom {Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) {U V : AlgebraicSpace S}
    (eU : U.toGroupoids ≌ Ucfg) (eV : V.toGroupoids ≌ Vcfg)
    (H : SheafOfModules.{u} (etaleRingedSite Ucfg).structureSheaf)
    (W : AlgebraicSpace.smallEtaleSite V) :
    limit (restrictDirectImageComparison_bigDiag a eV H W) ⟶
      limit (restrictDirectImageComparison_smallDiag a eU eV H W) :=
  limit.pre (restrictDirectImageComparison_bigDiag a eV H W)
      (restrictDirectImageComparison_indexMap a eU eV W) ≫
    (HasLimit.isoOfNatIso
      (restrictDirectImageComparison_diagIso a eU eV H W)).hom

/-- Evaluation of `a_small,*` of a restricted module at `W` compared with the
CFG pushforward at `u_V(W)`, via the two Kan-extension limits. -/
def restrictDirectImageComparison_rightEval {Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) {U V : AlgebraicSpace S}
    (eU : U.toGroupoids ≌ Ucfg) (eV : V.toGroupoids ≌ Vcfg)
    (H : SheafOfModules.{u} (etaleRingedSite Ucfg).structureSheaf)
    (W : AlgebraicSpace.smallEtaleSite V) :
    ((ToInternal.underlying (etaleRingedSite Ucfg).structureSheaf ⋙
          (etaleRingedToposHom a).toTopos.pushforward).obj H).obj.obj
        (op ((smallEtaleFunctor V Vcfg eV).obj W)) ⟶
      ((ToInternal.underlying (AlgebraicSpace.structureSheaf U) ⋙
            (AlgebraicSpace.ringedToposHom
                (moduleComparisonSpaceMorphism a eU eV)).toTopos.pushforward).obj
          ((restrictModules eU).obj H)).obj.obj (op W) :=
  ((toCartesianBasedFunctor a).toFunctor.op.ranObjObjIsoLimit
      ((ToInternal.underlying (etaleRingedSite Ucfg).structureSheaf).obj H).obj
      (op ((smallEtaleFunctor V Vcfg eV).obj W))).hom ≫
    restrictDirectImageComparison_limitHom a eU eV H W ≫
      (limit.isoLimitCone
        ⟨AlgebraicSpace.EtaleTopos.allChartCone U
          ((ToInternal.underlying (AlgebraicSpace.structureSheaf U)).obj ((restrictModules eU).obj H))
          ((AlgebraicSpace.etaleBaseChange (moduleComparisonSpaceMorphism a eU eV)).obj W),
         AlgebraicSpace.EtaleTopos.allChartIsLimit U
          ((ToInternal.underlying (AlgebraicSpace.structureSheaf U)).obj ((restrictModules eU).obj H))
          ((AlgebraicSpace.etaleBaseChange (moduleComparisonSpaceMorphism a eU eV)).obj W)⟩).hom

/-- Sectionwise underlying comparison `(a_* H)|_{V_étale}(W) ⟶ a_small,* (H|_{U_étale})(W)`. -/
def restrictDirectImageComparisonUnderlying_app {Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) {U V : AlgebraicSpace S}
    (eU : U.toGroupoids ≌ Ucfg) (eV : V.toGroupoids ≌ Vcfg)
    (H : SheafOfModules.{u} (etaleRingedSite Ucfg).structureSheaf)
    (W : AlgebraicSpace.smallEtaleSite V) :
    ((ToInternal.underlying (AlgebraicSpace.structureSheaf V)).obj
        ((restrictModules eV).obj ((etaleModuleDirectImage a).obj H))).obj.obj (op W) ⟶
      ((ToInternal.underlying (AlgebraicSpace.structureSheaf V)).obj
        (((AlgebraicSpace.ringedToposHom
            (moduleComparisonSpaceMorphism a eU eV)).modulePushforward).obj
          ((restrictModules eU).obj H))).obj.obj (op W) :=
  (restrictDirectImageComparison_leftEval a eV H W).hom ≫
    ((sheafToPresheaf Vcfg.etaleTopology (Type u)).map
        ((RingedSite.ToposHom.ModulePushforward.forgetIso
            (etaleRingedToposHom a)).hom.app H)).app
      (op ((smallEtaleFunctor V Vcfg eV).obj W)) ≫
      restrictDirectImageComparison_rightEval a eU eV H W ≫
        ((sheafToPresheaf (AlgebraicSpace.smallEtaleTopology V) (Type u)).map
            ((RingedSite.ToposHom.ModulePushforward.forgetIso
                (AlgebraicSpace.ringedToposHom
                  (moduleComparisonSpaceMorphism a eU eV))).inv.app
              ((restrictModules eU).obj H))).app (op W)

/-- Identification `restrict(h_* H) ⟶ h_small,* (restrict H)` of restricted
direct images, as an underlying type-valued sheaf morphism. -/
def restrictDirectImageComparisonUnderlying {Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) {U V : AlgebraicSpace S}
    (eU : U.toGroupoids ≌ Ucfg) (eV : V.toGroupoids ≌ Vcfg)
    (H : SheafOfModules.{u} (etaleRingedSite Ucfg).structureSheaf) :
    (ToInternal.underlying (AlgebraicSpace.structureSheaf V)).obj
        ((restrictModules eV).obj ((etaleModuleDirectImage a).obj H)) ⟶
      (ToInternal.underlying (AlgebraicSpace.structureSheaf V)).obj
        (((AlgebraicSpace.ringedToposHom
            (moduleComparisonSpaceMorphism a eU eV)).modulePushforward).obj
          ((restrictModules eU).obj H)) :=
  CategoryTheory.ObjectProperty.homMk
    { app := fun W => restrictDirectImageComparisonUnderlying_app a eU eV H W.unop
      naturality := sorry }

/-- Restriction of CFG direct image compared with small étale pushforward of the
restriction. -/
def restrictDirectImageComparison {Ucfg Vcfg : GroupoidsOver S} (a : Ucfg ⟶ Vcfg)
    {U V : AlgebraicSpace S} (eU : U.toGroupoids ≌ Ucfg) (eV : V.toGroupoids ≌ Vcfg)
    (H : SheafOfModules.{u} (etaleRingedSite Ucfg).structureSheaf) :
    (restrictModules eV).obj ((etaleModuleDirectImage a).obj H) ⟶
      ((AlgebraicSpace.ringedToposHom
          (moduleComparisonSpaceMorphism a eU eV)).modulePushforward).obj
        ((restrictModules eU).obj H) :=
  homOfUnderlying (AlgebraicSpace.structureSheaf V)
    (restrictDirectImageComparisonUnderlying a eU eV H) sorry sorry

/-- Comparison `a_small^*(G |_{V_étale}) ⟶ (a^* G)|_{U_étale}` of restricted
module sheaves on `U_étale`, the mate of the restricted CFG unit. -/
def restrictPullbackComparison {Ucfg Vcfg : GroupoidsOver S} (a : Ucfg ⟶ Vcfg)
    {U V : AlgebraicSpace S} (eU : U.toGroupoids ≌ Ucfg) (eV : V.toGroupoids ≌ Vcfg)
    (G : SheafOfModules.{u} (etaleRingedSite Vcfg).structureSheaf) :
    (AlgebraicSpace.Modules.pullback (moduleComparisonSpaceMorphism a eU eV)).obj
        ((restrictModules eV).obj G) ⟶
      (restrictModules eU).obj ((etaleModuleInverseImage a).obj G) :=
  ((AlgebraicSpace.Modules.pullbackPushforwardAdjunction
        (moduleComparisonSpaceMorphism a eU eV)).homEquiv
      ((restrictModules eV).obj G)
      ((restrictModules eU).obj ((etaleModuleInverseImage a).obj G))).symm
    ((restrictModules eV).map
        (etaleModuleUnit a G ≫
          (etaleModuleDirectImage a).map
            (etaleModulePullbackToInverseImage a G)) ≫
      restrictDirectImageComparison a eU eV ((etaleModuleInverseImage a).obj G))

/-- The restricted 2-cell `(a^* g^* F)|_{U_étale} ⟶ (f^* F)|_{U_étale}`. -/
def restrictTwoCell {X Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) (f : Ucfg ⟶ X) (g : Vcfg ⟶ X) (φ : a ≫ g ≅ f)
    {U : AlgebraicSpace S} (eU : U.toGroupoids ≌ Ucfg)
    (F : SheafOfModules.{u} (etaleRingedSite X).structureSheaf) :
    (restrictModules eU).obj
        ((etaleModuleInverseImage a).obj ((etaleModuleInverseImage g).obj F)) ⟶
      (restrictModules eU).obj ((etaleModuleInverseImage f).obj F) :=
  (restrictModules eU).map ((etaleModuleInverseImage_twoCell a f g φ).hom.app F)

/-- Unit of the small-étale module adjunction of the space morphism corresponding
to `a`, applied to a restricted sheaf on `V`. -/
def moduleComparisonSpaceUnit {Ucfg Vcfg : GroupoidsOver S} (a : Ucfg ⟶ Vcfg)
    {U V : AlgebraicSpace S} (eU : U.toGroupoids ≌ Ucfg) (eV : V.toGroupoids ≌ Vcfg)
    (N : SheafOfModules.{u} (AlgebraicSpace.structureSheaf V)) :
    N ⟶
      ((AlgebraicSpace.ringedToposHom (moduleComparisonSpaceMorphism a eU eV)).modulePushforward).obj
        ((AlgebraicSpace.Modules.pullback (moduleComparisonSpaceMorphism a eU eV)).obj N) :=
  (AlgebraicSpace.Modules.pullbackPushforwardAdjunction
        (moduleComparisonSpaceMorphism a eU eV)).unit.app N

/-- The push-form comparison
`g^* F |_{V_étale} ⟶ a_small,* (f^* F |_{U_étale})` of `𝒪_{V_étale}`-modules:
the unit of `a_small^* ⊣ a_small,*` after restriction, then transport along `φ`. -/
def moduleComparisonSpacePushforward {X Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) (f : Ucfg ⟶ X) (g : Vcfg ⟶ X) (φ : a ≫ g ≅ f)
    {U V : AlgebraicSpace S} (eU : U.toGroupoids ≌ Ucfg) (eV : V.toGroupoids ≌ Vcfg)
    (F : SheafOfModules.{u} (etaleRingedSite X).structureSheaf) :
    (restrictModules eV).obj ((etaleModuleInverseImage g).obj F) ⟶
      ((AlgebraicSpace.ringedToposHom (moduleComparisonSpaceMorphism a eU eV)).modulePushforward).obj
        ((restrictModules eU).obj ((etaleModuleInverseImage f).obj F)) :=
  (restrictModules eV).map
      (etaleModuleUnit a ((etaleModuleInverseImage g).obj F) ≫
        (etaleModuleDirectImage a).map
          (etaleModulePullbackToInverseImage a ((etaleModuleInverseImage g).obj F) ≫
            (etaleModuleInverseImage_twoCell a f g φ).hom.app F)) ≫
    restrictDirectImageComparison a eU eV ((etaleModuleInverseImage f).obj F)

/-- The comparison morphism
`c_φ : a_small^*(g^* F |_{V_étale}) ⟶ f^* F |_{U_étale}` of
`𝒪_{U_étale}`-modules, obtained as the adjunct of
`moduleComparisonSpacePushforward`. -/
def moduleComparisonSpace {X Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) (f : Ucfg ⟶ X) (g : Vcfg ⟶ X) (φ : a ≫ g ≅ f)
    {U V : AlgebraicSpace S} (eU : U.toGroupoids ≌ Ucfg) (eV : V.toGroupoids ≌ Vcfg)
    (F : SheafOfModules.{u} (etaleRingedSite X).structureSheaf) :
    (AlgebraicSpace.Modules.pullback (moduleComparisonSpaceMorphism a eU eV)).obj
        ((restrictModules eV).obj ((etaleModuleInverseImage g).obj F)) ⟶
      (restrictModules eU).obj ((etaleModuleInverseImage f).obj F) :=
  ((AlgebraicSpace.Modules.pullbackPushforwardAdjunction
        (moduleComparisonSpaceMorphism a eU eV)).homEquiv
      ((restrictModules eV).obj ((etaleModuleInverseImage g).obj F))
      ((restrictModules eU).obj ((etaleModuleInverseImage f).obj F))).symm
    (moduleComparisonSpacePushforward a f g φ eU eV F)

/-- `moduleComparisonSpace` is the adjunct of `moduleComparisonSpacePushforward`
along the small-étale module adjunction of `a`. -/
theorem moduleComparisonSpace_adjunct {X Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) (f : Ucfg ⟶ X) (g : Vcfg ⟶ X) (φ : a ≫ g ≅ f)
    {U V : AlgebraicSpace S} (eU : U.toGroupoids ≌ Ucfg) (eV : V.toGroupoids ≌ Vcfg)
    (F : SheafOfModules.{u} (etaleRingedSite X).structureSheaf) :
    (AlgebraicSpace.Modules.pullbackPushforwardAdjunction
        (moduleComparisonSpaceMorphism a eU eV)).homEquiv
        ((restrictModules eV).obj ((etaleModuleInverseImage g).obj F))
        ((restrictModules eU).obj ((etaleModuleInverseImage f).obj F))
        (moduleComparisonSpace a f g φ eU eV F) =
      moduleComparisonSpacePushforward a f g φ eU eV F :=
  sorry

/-- Source-semantic characterisation: the push-form of `c_φ` is the restricted
unit of `a_small^* ⊣ a_small,*`, transported along `φ`. -/
theorem moduleComparisonSpace_spec {X Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) (f : Ucfg ⟶ X) (g : Vcfg ⟶ X) (φ : a ≫ g ≅ f)
    {U V : AlgebraicSpace S} (eU : U.toGroupoids ≌ Ucfg) (eV : V.toGroupoids ≌ Vcfg)
    (F : SheafOfModules.{u} (etaleRingedSite X).structureSheaf) :
    moduleComparisonSpacePushforward a f g φ eU eV F =
      (restrictModules eV).map
          (etaleModuleUnit a ((etaleModuleInverseImage g).obj F) ≫
            (etaleModuleDirectImage a).map
              (etaleModulePullbackToInverseImage a
                  ((etaleModuleInverseImage g).obj F) ≫
                (etaleModuleInverseImage_twoCell a f g φ).hom.app F)) ≫
        restrictDirectImageComparison a eU eV
          ((etaleModuleInverseImage f).obj F) :=
  sorry

/-- Unfolding `moduleComparisonSpace` as the adjunct of the push form. -/
theorem moduleComparisonSpace_app {X Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) (f : Ucfg ⟶ X) (g : Vcfg ⟶ X) (φ : a ≫ g ≅ f)
    {U V : AlgebraicSpace S} (eU : U.toGroupoids ≌ Ucfg) (eV : V.toGroupoids ≌ Vcfg)
    (F : SheafOfModules.{u} (etaleRingedSite X).structureSheaf) :
    moduleComparisonSpace a f g φ eU eV F =
      ((AlgebraicSpace.Modules.pullbackPushforwardAdjunction
        (moduleComparisonSpaceMorphism a eU eV)).homEquiv
          ((restrictModules eV).obj ((etaleModuleInverseImage g).obj F))
          ((restrictModules eU).obj ((etaleModuleInverseImage f).obj F))).symm
        (moduleComparisonSpacePushforward a f g φ eU eV F) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
