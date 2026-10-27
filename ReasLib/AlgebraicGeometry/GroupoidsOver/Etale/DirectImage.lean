/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.Module
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.ModuleAdjunction
public import ReasLib.CategoryTheory.Fibered.InheritedTopology.Morphism
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.OneCell
public import ReasLib.CategoryTheory.Sites.Pushforward.SmallSectionsRing
public import ReasLib.CategoryTheory.Sites.Pushforward.SmallSectionsAdjunction

/-!
# Étale direct image with correctly sized sheaf sections

Inverse image is actual continuous precomposition. Small-coefficient
direct image requires only the genuine compatible sections of sheaves
to be small; no right extension of every arbitrary presheaf is asserted.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Functor
open FiberedCategoryOver.Groupoids
open RingedSite.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- The explicit size premise required to form a Type-`u` direct image along a CFG map. -/
class HasSmallCFGTypeSections {S : Scheme.{u}} {X Y : GroupoidsOver S} (h : X ⟶ Y) : Prop where
  small : ∀ F : Sheaf X.etaleTopology (Type u), ∀ Z : Y.totalᵒᵖ,
    Small.{u} (StructuredArrow.proj Z (toCartesianBasedFunctor h).toFunctor.op ⋙ F.obj).sections

/-- The cartesian total functor has the same underlying functor as the CFG map. -/
theorem cartesian_toFunctor_eq {X Y : GroupoidsOver S} (h : X ⟶ Y) :
    (toCartesianBasedFunctor h).toFunctor = toFunctor h :=
  congrArg (fun F => F.toFunctor) (toCartesianBasedFunctor.toBasedFunctor h)

/-- Compatible sections along the total functor are small under the CFG size premise. -/
instance (h : X ⟶ Y) [hP : HasSmallCFGTypeSections (S := S) h] :
    ∀ F : Sheaf X.etaleTopology (Type u), ∀ Z : Y.totalᵒᵖ,
      Small.{u} (StructuredArrow.proj Z (toFunctor h).op ⋙ F.obj).sections := by
  intro F Z
  rw [← cartesian_toFunctor_eq h]
  exact hP.small F Z

/-- A ring sheaf's actual underlying presheaf is a type-valued sheaf.
This is the algebraic sheaf law, without requiring all large-index ring limits. -/
instance etaleTopology_hasSheafCompose_ring_type (X : GroupoidsOver S) :
    X.etaleTopology.HasSheafCompose (forget RingCat.{u}) where
  isSheaf P hP := sorry

/-- The supplied cartesian total functor is a morphism of inherited étale sites. -/
instance toFunctor_isMorphismOfSites_etale {X Y : GroupoidsOver S} (h : X ⟶ Y) :
    IsMorphismOfSites X.etaleTopology Y.etaleTopology (toFunctor h) := sorry

/-- The cartesian total functor of a CFG morphism is continuous for the inherited étale topologies. -/
instance toCartesianBasedFunctor_isContinuous_etale {X Y : GroupoidsOver S} (h : X ⟶ Y) :
    (toCartesianBasedFunctor h).toFunctor.IsContinuous X.etaleTopology Y.etaleTopology :=
  CartesianBasedFunctor.inheritedTopology.isContinuous
    (toCartesianBasedFunctor h) (StandardTopology.etale.overTopology S)

/-- The cartesian total functor of a CFG morphism is cocontinuous for the inherited étale topologies. -/
instance toCartesianBasedFunctor_isCocontinuous_etale {X Y : GroupoidsOver S} (h : X ⟶ Y) :
    (toCartesianBasedFunctor h).toFunctor.IsCocontinuous X.etaleTopology Y.etaleTopology :=
  CartesianBasedFunctor.inheritedTopology.isCocontinuous
    (toCartesianBasedFunctor h) (StandardTopology.etale.overTopology S)

/-- A CFG morphism is continuous for the associated étale topologies. -/
instance toFunctor_isContinuous_etale {X Y : GroupoidsOver S} (h : X ⟶ Y) :
    (toFunctor h).IsContinuous X.etaleTopology Y.etaleTopology :=
  (toFunctor_isMorphismOfSites_etale h).toIsContinuous

/-- A CFG morphism followed by the target projection is étale-continuous. -/
instance toFunctor_comp_p_isContinuous_etale {X Y : GroupoidsOver S} (h : X ⟶ Y) :
    (toFunctor h ⋙ Y.p).IsContinuous X.etaleTopology
      (StandardTopology.etale.overTopology S) :=
  Functor.isContinuous_of_iso (eqToIso (comm h).symm) X.etaleTopology
    (StandardTopology.etale.overTopology S)

/-- A CFG morphism is cocontinuous for the associated étale topologies. -/
instance toFunctor_isCocontinuous_etale {X Y : GroupoidsOver S} (h : X ⟶ Y) :
    (toFunctor h).IsCocontinuous X.etaleTopology Y.etaleTopology :=
  CartesianBasedFunctor.inheritedTopology.isCocontinuous
    (toCartesianBasedFunctor h) (StandardTopology.etale.overTopology S)

/-- The identification `f⁻¹ 𝒪_Y ≅ 𝒪_X` of commutative étale structure sheaves. -/
def commEtaleStructureSheafIso {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    ((toFunctor f).sheafPushforwardContinuous CommRingCat.{u}
        X.etaleTopology Y.etaleTopology).obj (commEtaleStructureSheaf Y) ≅
      commEtaleStructureSheaf X :=
  (sheafPushforwardContinuousComp' (eqToIso (comm f)) CommRingCat.{u}
      X.etaleTopology Y.etaleTopology
      (StandardTopology.etale.overTopology S)).app bigEtaleCommStructureSheaf

/-- The underlying ring sheaf of `f⁻¹ 𝒪_Y` is the inverse image of the underlying ring sheaf. -/
def inverseImageEtaleStructureSheafIso {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    CategoryTheory.Sheaf.ringSheafOfComm.{u, u + 1, u}
      (((toFunctor f).sheafPushforwardContinuous CommRingCat.{u}
          X.etaleTopology Y.etaleTopology).obj (commEtaleStructureSheaf Y)) ≅
      ((toFunctor f).sheafPushforwardContinuous RingCat.{u}
        X.etaleTopology Y.etaleTopology).obj (etaleStructureSheaf Y) :=
  (fullyFaithfulSheafToPresheaf X.etaleTopology RingCat.{u}).preimageIso (Iso.refl _)

/-- The coefficient map `𝒪_X ⟶ f⁻¹ 𝒪_Y` is the canonical structure-sheaf comparison. -/
def etaleSiteHom_structureSheafMap {X Y : GroupoidsOver S} (h : X ⟶ Y) :
    (etaleRingedSite X).structureSheaf ⟶
      ((toFunctor h).sheafPushforwardContinuous RingCat.{u}
        X.etaleTopology Y.etaleTopology).obj (etaleRingedSite Y).structureSheaf :=
  CategoryTheory.Sheaf.ringSheafOfCommMap.{u, u + 1, u} (commEtaleStructureSheafIso h).inv ≫
    (inverseImageEtaleStructureSheafIso h).hom

/-- The canonical étale coefficient map is an isomorphism. -/
instance etaleSiteHom_structureSheafMap_isIso {X Y : GroupoidsOver S} (h : X ⟶ Y) :
    IsIso (etaleSiteHom_structureSheafMap h) := by
  unfold etaleSiteHom_structureSheafMap
  infer_instance

/-- A CFG morphism induces a morphism of étale ringed sites in the inverse-image direction. -/
def etaleSiteHom {X Y : GroupoidsOver S} (h : X ⟶ Y) :
    RingedSite.Hom (etaleRingedSite Y) (etaleRingedSite X) where
  base := toFunctor h
  isMorphismOfSites := toFunctor_isMorphismOfSites_etale h
  structureSheafMap := etaleSiteHom_structureSheafMap h

/-- Inverse image of étale modules along a CFG morphism, with its canonical coefficient map. -/
def etaleModuleInverseImage {X Y : GroupoidsOver S} (h : X ⟶ Y) :
    SheafOfModules.{u} (etaleRingedSite Y).structureSheaf ⥤
      SheafOfModules.{u} (etaleRingedSite X).structureSheaf :=
  (etaleSiteHom h).modulePushforward.{u}

/-- Étale module inverse image is module pushforward along the induced ringed-site morphism. -/
theorem etaleModuleInverseImage_eq {X Y : GroupoidsOver S} (h : X ⟶ Y) :
    etaleModuleInverseImage h = (etaleSiteHom h).modulePushforward.{u} := rfl

/-- The structure sheaf on the source is obtained from the target by continuous precomposition. -/
def etaleModuleStructureSheafInv {X Y : GroupoidsOver S} (h : X ⟶ Y) :
    ((toFunctor h).sheafPushforwardContinuous RingCat.{u}
        X.etaleTopology Y.etaleTopology).obj (etaleRingedSite Y).structureSheaf ⟶
      (etaleRingedSite X).structureSheaf :=
  (sheafPushforwardContinuousIso (eqToIso (comm h).symm) RingCat.{u}
      X.etaleTopology (StandardTopology.etale.overTopology S)).inv.app
    (StandardTopology.Big.structureSheaf StandardTopology.etale S)

section DirectImage

variable {X Y : GroupoidsOver S} (h : X ⟶ Y)
variable [hType : HasSmallCFGTypeSections (S := S) h]

/-- Direct structure morphism, using the actual ring-sheaf transposition. -/
def etaleModuleStructureSheafMap :
    (etaleRingedSite Y).structureSheaf ⟶
      ((toFunctor h).sheafPushforwardRingOfSmallSections.{u + 1, u, u + 1, u, u}
        X.etaleTopology Y.etaleTopology).obj (etaleRingedSite X).structureSheaf :=
  ((toFunctor h).sheafPushforwardRingOfSmallSectionsAdjunction.{u + 1, u, u + 1, u, u}
    X.etaleTopology Y.etaleTopology).homEquiv _ _ (etaleModuleStructureSheafInv h)

/-- The transposed direct structure morphism respects the ring structures. -/
theorem etaleModuleStructureSheafMap_isRingCompatible :
    @RingedSite.ToposHom.Direct.IsRingCompatible
      (etaleRingedSite X) (etaleRingedSite Y) inferInstance inferInstance
      ((toFunctor h).morphismOfTopoiOfSmallSheafSections.{u + 1, u, u + 1, u, u}
        X.etaleTopology Y.etaleTopology)
      ((toFunctor h).sheafPushforwardRingOfSmallSections.{u + 1, u, u + 1, u, u} X.etaleTopology Y.etaleTopology)
      ((toFunctor h).sheafPushforwardRingOfSmallSectionsForgetIso.{u + 1, u, u + 1, u, u} X.etaleTopology Y.etaleTopology)
      (etaleModuleStructureSheafMap h) := sorry

/-- A small-coefficient morphism of ringed topoi with size at the actual sheaf section boundary. -/
def etaleRingedToposHom : RingedSite.ToposHom (etaleRingedSite X) (etaleRingedSite Y) :=
  RingedSite.ToposHom.ofDirectImage.{u + 1, u, u + 1, u, u}
    ((toFunctor h).morphismOfTopoiOfSmallSheafSections.{u + 1, u, u + 1, u, u} X.etaleTopology Y.etaleTopology)
    ((toFunctor h).sheafPushforwardRingOfSmallSections.{u + 1, u, u + 1, u, u} X.etaleTopology Y.etaleTopology)
    ((toFunctor h).sheafPushforwardRingOfSmallSectionsForgetIso.{u + 1, u, u + 1, u, u} X.etaleTopology Y.etaleTopology)
    (etaleModuleStructureSheafMap h) (etaleModuleStructureSheafMap_isRingCompatible h)

/-- Direct image of étale modules with small compatible sheaf sections. -/
def etaleModuleDirectImage :
    SheafOfModules.{u} (etaleRingedSite X).structureSheaf ⥤
      SheafOfModules.{u} (etaleRingedSite Y).structureSheaf :=
  (etaleRingedToposHom h).modulePushforward

/-- Étale module direct image is pushforward along the induced morphism of ringed topoi. -/
theorem etaleModuleDirectImage_eq :
    etaleModuleDirectImage h = (etaleRingedToposHom h).modulePushforward := rfl

end DirectImage

end AlgebraicGeometry.GroupoidsOver
