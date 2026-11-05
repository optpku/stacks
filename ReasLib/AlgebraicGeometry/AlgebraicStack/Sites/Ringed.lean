/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import ReasLib.AlgebraicGeometry.RingedSite.Module.LowerShriek
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Cocontinuous.StructureIso
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.Module
public import ReasLib.AlgebraicGeometry.GroupoidsOver.StructureSheaf
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Restriction
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Sites.Topos

/-!
# Restricted structure sheaves and ringed morphisms of topoi

Restriction of `𝒪_X` along the lisse-étale and flat-fppf inclusions yields the
structure sheaves of the small sites. The resulting morphisms of ringed topoi
have invertible structure maps, so geometric inverse image agrees with module
pullback and is exact. Explicit sheafification and Kan-extension premises
express the bounded-site size convention.
-/

set_option backward.privateInPublic true

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.GroupoidsOver CategoryTheory
open CategoryTheory.Functor CategoryTheory.Limits
open RingedSite.Cocontinuous
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

section RestrictionComparison

universe u₁ u₂ v₁ v₂ w

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable (G : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable [HasWeakSheafify J (Type w)] [HasWeakSheafify K (Type w)]
variable [G.IsContinuous J K] [G.IsCocontinuous J K]
variable [∀ P : Cᵒᵖ ⥤ Type w, G.op.HasPointwiseRightKanExtension P]

/-- For a continuous and cocontinuous functor, the inverse restriction comparison
is the sheafification unit. This identifies the two inverse-map formulas below. -/
private theorem restrictionComparisonIso_inv_hom (F : Sheaf K (Type w)) :
    ((CocontinuousPullback.comparisonIso G J K).inv.app F).hom =
      toSheafify J (G.op ⋙ F.obj) := by
  apply (cancel_mono ((CocontinuousPullback.comparisonIso G J K).hom.app F).hom).1
  rw [← ObjectProperty.FullSubcategory.comp_hom, Iso.inv_hom_id_app, ObjectProperty.FullSubcategory.id_hom]
  change 𝟙 _ = toSheafify J (G.op ⋙ F.obj) ≫
    ((G.pushforwardContinuousSheafificationCompatibility (Type w) J K).hom.app F.obj).hom ≫
      whiskerLeft G.op (sheafificationIso F).inv.hom
  rw [← Category.assoc, G.toSheafify_pullbackSheafificationCompatibility]
  change 𝟙 _ = whiskerLeft G.op (sheafificationIso F).hom.hom ≫
    whiskerLeft G.op (sheafificationIso F).inv.hom
  rw [← whiskerLeft_comp]
  simp

end RestrictionComparison

variable {S : Scheme.{u}}

/-- The structure sheaf `𝒪_{X_lisse,étale}` is the restriction of the étale
structure sheaf along the lisse-étale inclusion. -/
abbrev lisseEtaleStructureSheaf (X : GroupoidsOver S) [AlgebraicStack X] :
    Sheaf (lisseEtaleTopology X) RingCat.{u} :=
  inverseImageRingSheaf (lisseEtaleInclusion X) (etaleStructureSheaf X)

/-- `lisseEtaleStructureSheaf` is continuous pushforward of `etaleStructureSheaf`. -/
theorem lisseEtaleStructureSheaf_eq (X : GroupoidsOver S) [AlgebraicStack X] :
    lisseEtaleStructureSheaf X =
      ((lisseEtaleInclusion X).sheafPushforwardContinuous RingCat.{u}
        (lisseEtaleTopology X) X.etaleTopology).obj (etaleStructureSheaf X) :=
  rfl

/-- The lisse-étale site of `X`, ringed by the restricted structure sheaf. -/
abbrev lisseEtaleRingedSite (X : GroupoidsOver S) [AlgebraicStack X] :
    RingedSite.{u + 1, u, u} :=
  RingedSite.ofRingSheaf (lisseEtaleTopology X) (lisseEtaleStructureSheaf X)

/-- The structure sheaf of `lisseEtaleRingedSite X` is `lisseEtaleStructureSheaf X`. -/
theorem lisseEtaleRingedSite_structureSheaf (X : GroupoidsOver S)
    [AlgebraicStack X] :
    (lisseEtaleRingedSite X).structureSheaf = lisseEtaleStructureSheaf X :=
  rfl

/-- The restriction comparison for structure presheaves, with its explicit inverse. -/
def lisseEtaleStructurePresheafIso (X : GroupoidsOver S) [AlgebraicStack X] :
    (lisseEtaleInclusion X).op ⋙ (etaleStructureSheaf X).obj ≅
      (lisseEtaleStructureSheaf X).obj :=
  (((lisseEtaleInclusion X).sheafPushforwardContinuousCompSheafToPresheafIso
      RingCat.{u} (lisseEtaleTopology X) X.etaleTopology).app (etaleStructureSheaf X)).symm

/-- The identity/restriction map of structure sheaves as ring presheaves. -/
def lisseEtaleStructurePresheafHom (X : GroupoidsOver S) [AlgebraicStack X] :
    (lisseEtaleInclusion X).op ⋙ (etaleStructureSheaf X).obj ⟶
      (lisseEtaleStructureSheaf X).obj :=
  (lisseEtaleStructurePresheafIso X).hom

/-- `lisseEtaleStructurePresheafHom` is the inverse of the continuous-pushforward
comparison on `etaleStructureSheaf`. -/
theorem lisseEtaleStructurePresheafHom_eq (X : GroupoidsOver S)
    [AlgebraicStack X] :
    lisseEtaleStructurePresheafHom X =
      ((lisseEtaleInclusion X).sheafPushforwardContinuousCompSheafToPresheafIso
          RingCat.{u} (lisseEtaleTopology X) X.etaleTopology).inv.app
        (etaleStructureSheaf X) :=
  rfl

/-- The morphism of ringed topoi induced by the lisse-étale inclusion, with
identity restriction map on structure sheaves. -/
def lisseEtaleRingedToposHom (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u,
      (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P]
    [(lisseEtaleTopology X).HasSheafCompose (forget RingCat.{u})]
    [X.etaleTopology.HasSheafCompose (forget RingCat.{u})] :
    RingedSite.ToposHom (lisseEtaleRingedSite X) (etaleRingedSite X) :=
  toRingedTopos (X := lisseEtaleRingedSite X) (Y := etaleRingedSite X)
    (lisseEtaleInclusion X) (lisseEtaleStructurePresheafHom X)

/-- The underlying morphism of topoi of `lisseEtaleRingedToposHom` is
`lisseEtaleToposHom`. -/
theorem lisseEtaleRingedToposHom_toTopos (X : GroupoidsOver S)
    [AlgebraicStack X]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u,
      (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P]
    [(lisseEtaleTopology X).HasSheafCompose (forget RingCat.{u})]
    [X.etaleTopology.HasSheafCompose (forget RingCat.{u})] :
    (lisseEtaleRingedToposHom X).toTopos = lisseEtaleToposHom X :=
  rfl

/-- The inverse structure map is the public cocontinuous construction through
 the presheaf inverse, sheafification unit, and coefficient-forgetful comparison. -/
def lisseEtaleStructureSheafIsoInv (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u,
      (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P]
    [(lisseEtaleTopology X).HasSheafCompose (forget RingCat.{u})]
    [X.etaleTopology.HasSheafCompose (forget RingCat.{u})]
    [HasSheafify X.etaleTopology (Type u)] :
    lisseEtaleStructureSheaf X ⟶ (lisseEtaleToposHom X).ringInverseImage.obj (etaleStructureSheaf X) :=
  structureMapInv (X := lisseEtaleRingedSite X) (Y := etaleRingedSite X)
    (lisseEtaleInclusion X) (lisseEtaleStructurePresheafIso X)

/-- The structure-sheaf comparison specializes the public cocontinuous isomorphism. -/
def lisseEtaleStructureSheafIso (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u,
      (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P]
    [(lisseEtaleTopology X).HasSheafCompose (forget RingCat.{u})]
    [X.etaleTopology.HasSheafCompose (forget RingCat.{u})]
    [HasSheafify X.etaleTopology (Type u)] :
    (lisseEtaleToposHom X).ringInverseImage.obj (etaleStructureSheaf X) ≅ lisseEtaleStructureSheaf X :=
  structureMapIso (X := lisseEtaleRingedSite X) (Y := etaleRingedSite X)
    (lisseEtaleInclusion X) (lisseEtaleStructurePresheafIso X)

/-- The forward comparison is the original structure map. -/
@[simp]
theorem lisseEtaleStructureSheafIso_hom (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u,
      (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P]
    [(lisseEtaleTopology X).HasSheafCompose (forget RingCat.{u})]
    [X.etaleTopology.HasSheafCompose (forget RingCat.{u})]
    [HasSheafify X.etaleTopology (Type u)] :
    (lisseEtaleStructureSheafIso X).hom = (lisseEtaleRingedToposHom X).structureMap := rfl

/-- The inverse comparison is the specified inverse structure map. -/
@[simp]
theorem lisseEtaleStructureSheafIso_inv (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u,
      (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P]
    [(lisseEtaleTopology X).HasSheafCompose (forget RingCat.{u})]
    [X.etaleTopology.HasSheafCompose (forget RingCat.{u})]
    [HasSheafify X.etaleTopology (Type u)] :
    (lisseEtaleStructureSheafIso X).inv = lisseEtaleStructureSheafIsoInv X := rfl

/-- The public inverse construction retains the original restriction-comparison
formula on sections. -/
theorem lisseEtaleStructureSheafIsoInv_app (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u,
      (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P]
    [(lisseEtaleTopology X).HasSheafCompose (forget RingCat.{u})]
    [X.etaleTopology.HasSheafCompose (forget RingCat.{u})]
    [HasSheafify X.etaleTopology (Type u)]
    (U : (lisseEtaleSite X)ᵒᵖ) (r : (lisseEtaleStructureSheaf X).obj.obj U) :
    ((lisseEtaleStructureSheafIsoInv X).hom.app U).hom r =
      ((CocontinuousPullback.comparisonIso (lisseEtaleInclusion X)
          (lisseEtaleTopology X) X.etaleTopology).inv.app
          ((sheafCompose X.etaleTopology (forget RingCat.{u})).obj (etaleStructureSheaf X)) ≫
        (lisseEtaleToposHom X).ringInverseImageForgetIso.inv.app (etaleStructureSheaf X)).hom.app U r := by
  change (structureMapInverseUnderlying (X := lisseEtaleRingedSite X) (Y := etaleRingedSite X)
    (lisseEtaleInclusion X) (lisseEtaleStructurePresheafIso X)).hom.app U r = _
  simp only [structureMapInverseUnderlying, ObjectProperty.FullSubcategory.comp_hom,
    restrictionComparisonIso_inv_hom]
  rfl

/-- The structure map of the restricted ringed morphism is invertible. -/
theorem lisseEtaleRingedToposHom.structureMap_isIso (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u,
      (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P]
    [(lisseEtaleTopology X).HasSheafCompose (forget RingCat.{u})]
    [X.etaleTopology.HasSheafCompose (forget RingCat.{u})]
    [HasSheafify X.etaleTopology (Type u)] :
    IsIso (lisseEtaleRingedToposHom X).structureMap :=
  (lisseEtaleStructureSheafIso X).isIso_hom

/-- Restriction of scalars along the structure map is a right adjoint. -/
theorem lisseEtaleRingedToposHom.restrictScalars_isRightAdjoint (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u,
      (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P]
    [(lisseEtaleTopology X).HasSheafCompose (forget RingCat.{u})]
    [X.etaleTopology.HasSheafCompose (forget RingCat.{u})]
    [HasSheafify X.etaleTopology (Type u)] :
    (SheafOfModules.restrictScalars.{u} (lisseEtaleRingedToposHom X).structureMap).IsRightAdjoint :=
  (SheafOfModules.Restriction.equivalenceOfIso.{u} (lisseEtaleStructureSheafIso X)).isRightAdjoint_inverse

/-- Module pullback along the restricted ringed morphism, with its canonical scalar adjunction. -/
def lisseEtaleModulePullback (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u,
      (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P]
    [(lisseEtaleTopology X).HasSheafCompose (forget RingCat.{u})]
    [X.etaleTopology.HasSheafCompose (forget RingCat.{u})]
    [HasSheafify X.etaleTopology (Type u)] :
    SheafOfModules.{u} (etaleRingedSite X).structureSheaf ⥤
      SheafOfModules.{u} (lisseEtaleStructureSheaf X) :=
  @RingedSite.ToposHom.modulePullback _ _ inferInstance inferInstance
    (lisseEtaleRingedToposHom X) (lisseEtaleRingedToposHom.restrictScalars_isRightAdjoint X)

/-- Module pullback factors as geometric inverse image and extension of scalars. -/
theorem lisseEtaleRingedToposHom_modulePullback_eq (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u,
      (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P]
    [(lisseEtaleTopology X).HasSheafCompose (forget RingCat.{u})]
    [X.etaleTopology.HasSheafCompose (forget RingCat.{u})]
    [HasSheafify X.etaleTopology (Type u)] :
    lisseEtaleModulePullback X =
      (lisseEtaleToposHom X).moduleInverseImage (etaleStructureSheaf X) ⋙
        @SheafOfModules.ChangeOfRings.extendScalars _ _ _ _ _
          (lisseEtaleRingedToposHom X).structureMap
          (lisseEtaleRingedToposHom.restrictScalars_isRightAdjoint X) := rfl

/-- Module pullback is geometric inverse image transported through the structure-sheaf isomorphism. -/
def lisseEtaleModulePullbackRestrictionIso (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u,
      (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P]
    [(lisseEtaleTopology X).HasSheafCompose (forget RingCat.{u})]
    [X.etaleTopology.HasSheafCompose (forget RingCat.{u})]
    [HasSheafify X.etaleTopology (Type u)] :
    lisseEtaleModulePullback X ≅
      (lisseEtaleToposHom X).moduleInverseImage (etaleStructureSheaf X) ⋙
        SheafOfModules.restrictScalars.{u} (lisseEtaleStructureSheafIso X).inv :=
  Functor.isoWhiskerLeft ((lisseEtaleToposHom X).moduleInverseImage (etaleStructureSheaf X))
    (Adjunction.leftAdjointUniq
      (@SheafOfModules.ChangeOfRings.extendRestrictAdjunction _ _ _ _ _
        (lisseEtaleRingedToposHom X).structureMap
        (lisseEtaleRingedToposHom.restrictScalars_isRightAdjoint X))
      (SheafOfModules.Restriction.equivalenceOfIso.{u}
        (lisseEtaleStructureSheafIso X)).toAdjunction)

/-- Module pullback along the restricted ringed morphism preserves finite limits. -/
theorem lisseEtaleRingedToposHom.modulePullback_preservesFiniteLimits (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u,
      (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P]
    [(lisseEtaleTopology X).HasSheafCompose (forget RingCat.{u})]
    [X.etaleTopology.HasSheafCompose (forget RingCat.{u})]
    [HasSheafify X.etaleTopology (Type u)] :
    PreservesFiniteLimits (lisseEtaleModulePullback X) := sorry

/-- Module pullback along the restricted ringed morphism preserves finite colimits. -/
theorem lisseEtaleRingedToposHom.modulePullback_preservesFiniteColimits (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u,
      (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P]
    [(lisseEtaleTopology X).HasSheafCompose (forget RingCat.{u})]
    [X.etaleTopology.HasSheafCompose (forget RingCat.{u})]
    [HasSheafify X.etaleTopology (Type u)] :
    PreservesFiniteColimits (lisseEtaleModulePullback X) := sorry

/-- The structure sheaf `𝒪_{X_flat,fppf}` is the restriction of `𝒪_X` along the
flat-fppf inclusion. -/
abbrev flatFppfStructureSheaf (X : GroupoidsOver S) [AlgebraicStack X] :
    Sheaf (flatFppfTopology X) RingCat.{u} :=
  inverseImageRingSheaf (flatFppfInclusion X) (structureSheaf X)

/-- `flatFppfStructureSheaf` is continuous pushforward of `structureSheaf`. -/
theorem flatFppfStructureSheaf_eq (X : GroupoidsOver S) [AlgebraicStack X] :
    flatFppfStructureSheaf X =
      ((flatFppfInclusion X).sheafPushforwardContinuous RingCat.{u}
        (flatFppfTopology X) (inheritedFppfTopology X)).obj (structureSheaf X) :=
  rfl

/-- The flat-fppf site of `X`, ringed by the restricted structure sheaf. -/
abbrev flatFppfRingedSite (X : GroupoidsOver S) [AlgebraicStack X] :
    RingedSite.{u + 1, u, u} :=
  RingedSite.ofRingSheaf (flatFppfTopology X) (flatFppfStructureSheaf X)

/-- The structure sheaf of `flatFppfRingedSite X` is `flatFppfStructureSheaf X`. -/
theorem flatFppfRingedSite_structureSheaf (X : GroupoidsOver S)
    [AlgebraicStack X] :
    (flatFppfRingedSite X).structureSheaf = flatFppfStructureSheaf X :=
  rfl

/-- The restriction comparison for structure presheaves, with its explicit inverse. -/
def flatFppfStructurePresheafIso (X : GroupoidsOver S) [AlgebraicStack X] :
    (flatFppfInclusion X).op ⋙ (structureSheaf X).obj ≅
      (flatFppfStructureSheaf X).obj :=
  (((flatFppfInclusion X).sheafPushforwardContinuousCompSheafToPresheafIso
      RingCat.{u} (flatFppfTopology X) (inheritedFppfTopology X)).app (structureSheaf X)).symm

/-- The identity/restriction map of structure sheaves as ring presheaves. -/
def flatFppfStructurePresheafHom (X : GroupoidsOver S) [AlgebraicStack X] :
    (flatFppfInclusion X).op ⋙ (structureSheaf X).obj ⟶
      (flatFppfStructureSheaf X).obj :=
  (flatFppfStructurePresheafIso X).hom

/-- `flatFppfStructurePresheafHom` is the inverse of the continuous-pushforward
comparison on `structureSheaf`. -/
theorem flatFppfStructurePresheafHom_eq (X : GroupoidsOver S)
    [AlgebraicStack X] :
    flatFppfStructurePresheafHom X =
      ((flatFppfInclusion X).sheafPushforwardContinuousCompSheafToPresheafIso
          RingCat.{u} (flatFppfTopology X) (inheritedFppfTopology X)).inv.app
        (structureSheaf X) :=
  rfl

/-- The morphism of ringed topoi induced by the flat-fppf inclusion, with
identity restriction map on structure sheaves. -/
def flatFppfRingedToposHom (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u,
      (flatFppfInclusion X).op.HasPointwiseRightKanExtension P]
    [(flatFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology X).HasSheafCompose (forget RingCat.{u})] :
    RingedSite.ToposHom (flatFppfRingedSite X) (ringedSite X) :=
  toRingedTopos (X := flatFppfRingedSite X) (Y := ringedSite X)
    (flatFppfInclusion X) (flatFppfStructurePresheafHom X)

/-- The underlying morphism of topoi of `flatFppfRingedToposHom` is
`flatFppfToposHom`. -/
theorem flatFppfRingedToposHom_toTopos (X : GroupoidsOver S)
    [AlgebraicStack X]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u,
      (flatFppfInclusion X).op.HasPointwiseRightKanExtension P]
    [(flatFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology X).HasSheafCompose (forget RingCat.{u})] :
    (flatFppfRingedToposHom X).toTopos = flatFppfToposHom X :=
  rfl

/-- The inverse structure map is the public cocontinuous construction through
 the presheaf inverse, sheafification unit, and coefficient-forgetful comparison. -/
def flatFppfStructureSheafIsoInv (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u,
      (flatFppfInclusion X).op.HasPointwiseRightKanExtension P]
    [(flatFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [HasSheafify (inheritedFppfTopology X) (Type u)] :
    flatFppfStructureSheaf X ⟶ (flatFppfToposHom X).ringInverseImage.obj (structureSheaf X) :=
  structureMapInv (X := flatFppfRingedSite X) (Y := ringedSite X)
    (flatFppfInclusion X) (flatFppfStructurePresheafIso X)

/-- The structure-sheaf comparison specializes the public cocontinuous isomorphism. -/
def flatFppfStructureSheafIso (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u,
      (flatFppfInclusion X).op.HasPointwiseRightKanExtension P]
    [(flatFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [HasSheafify (inheritedFppfTopology X) (Type u)] :
    (flatFppfToposHom X).ringInverseImage.obj (structureSheaf X) ≅ flatFppfStructureSheaf X :=
  structureMapIso (X := flatFppfRingedSite X) (Y := ringedSite X)
    (flatFppfInclusion X) (flatFppfStructurePresheafIso X)

/-- The forward comparison is the original structure map. -/
@[simp]
theorem flatFppfStructureSheafIso_hom (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u,
      (flatFppfInclusion X).op.HasPointwiseRightKanExtension P]
    [(flatFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [HasSheafify (inheritedFppfTopology X) (Type u)] :
    (flatFppfStructureSheafIso X).hom = (flatFppfRingedToposHom X).structureMap := rfl

/-- The inverse comparison is the specified inverse structure map. -/
@[simp]
theorem flatFppfStructureSheafIso_inv (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u,
      (flatFppfInclusion X).op.HasPointwiseRightKanExtension P]
    [(flatFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [HasSheafify (inheritedFppfTopology X) (Type u)] :
    (flatFppfStructureSheafIso X).inv = flatFppfStructureSheafIsoInv X := rfl

/-- The public inverse construction retains the original restriction-comparison
formula on sections. -/
theorem flatFppfStructureSheafIsoInv_app (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u,
      (flatFppfInclusion X).op.HasPointwiseRightKanExtension P]
    [(flatFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [HasSheafify (inheritedFppfTopology X) (Type u)]
    (U : (flatFppfSite X)ᵒᵖ) (r : (flatFppfStructureSheaf X).obj.obj U) :
    ((flatFppfStructureSheafIsoInv X).hom.app U).hom r =
      ((CocontinuousPullback.comparisonIso (flatFppfInclusion X)
          (flatFppfTopology X) (inheritedFppfTopology X)).inv.app
          ((sheafCompose (inheritedFppfTopology X) (forget RingCat.{u})).obj (structureSheaf X)) ≫
        (flatFppfToposHom X).ringInverseImageForgetIso.inv.app (structureSheaf X)).hom.app U r := by
  change (structureMapInverseUnderlying (X := flatFppfRingedSite X) (Y := ringedSite X)
    (flatFppfInclusion X) (flatFppfStructurePresheafIso X)).hom.app U r = _
  simp only [structureMapInverseUnderlying, ObjectProperty.FullSubcategory.comp_hom,
    restrictionComparisonIso_inv_hom]
  rfl

/-- The structure map of the restricted ringed morphism is invertible. -/
theorem flatFppfRingedToposHom.structureMap_isIso (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u,
      (flatFppfInclusion X).op.HasPointwiseRightKanExtension P]
    [(flatFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [HasSheafify (inheritedFppfTopology X) (Type u)] :
    IsIso (flatFppfRingedToposHom X).structureMap :=
  (flatFppfStructureSheafIso X).isIso_hom

/-- Restriction of scalars along the structure map is a right adjoint. -/
theorem flatFppfRingedToposHom.restrictScalars_isRightAdjoint (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u,
      (flatFppfInclusion X).op.HasPointwiseRightKanExtension P]
    [(flatFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [HasSheafify (inheritedFppfTopology X) (Type u)] :
    (SheafOfModules.restrictScalars.{u} (flatFppfRingedToposHom X).structureMap).IsRightAdjoint :=
  (SheafOfModules.Restriction.equivalenceOfIso.{u} (flatFppfStructureSheafIso X)).isRightAdjoint_inverse

/-- Module pullback along the restricted ringed morphism, with its canonical scalar adjunction. -/
def flatFppfModulePullback (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u,
      (flatFppfInclusion X).op.HasPointwiseRightKanExtension P]
    [(flatFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [HasSheafify (inheritedFppfTopology X) (Type u)] :
    SheafOfModules.{u} (ringedSite X).structureSheaf ⥤
      SheafOfModules.{u} (flatFppfStructureSheaf X) :=
  @RingedSite.ToposHom.modulePullback _ _ inferInstance inferInstance
    (flatFppfRingedToposHom X) (flatFppfRingedToposHom.restrictScalars_isRightAdjoint X)

/-- Module pullback factors as geometric inverse image and extension of scalars. -/
theorem flatFppfRingedToposHom_modulePullback_eq (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u,
      (flatFppfInclusion X).op.HasPointwiseRightKanExtension P]
    [(flatFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [HasSheafify (inheritedFppfTopology X) (Type u)] :
    flatFppfModulePullback X =
      (flatFppfToposHom X).moduleInverseImage (structureSheaf X) ⋙
        @SheafOfModules.ChangeOfRings.extendScalars _ _ _ _ _
          (flatFppfRingedToposHom X).structureMap
          (flatFppfRingedToposHom.restrictScalars_isRightAdjoint X) := rfl

/-- Module pullback is geometric inverse image transported through the structure-sheaf isomorphism. -/
def flatFppfModulePullbackRestrictionIso (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u,
      (flatFppfInclusion X).op.HasPointwiseRightKanExtension P]
    [(flatFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [HasSheafify (inheritedFppfTopology X) (Type u)] :
    flatFppfModulePullback X ≅
      (flatFppfToposHom X).moduleInverseImage (structureSheaf X) ⋙
        SheafOfModules.restrictScalars.{u} (flatFppfStructureSheafIso X).inv :=
  Functor.isoWhiskerLeft ((flatFppfToposHom X).moduleInverseImage (structureSheaf X))
    (Adjunction.leftAdjointUniq
      (@SheafOfModules.ChangeOfRings.extendRestrictAdjunction _ _ _ _ _
        (flatFppfRingedToposHom X).structureMap
        (flatFppfRingedToposHom.restrictScalars_isRightAdjoint X))
      (SheafOfModules.Restriction.equivalenceOfIso.{u}
        (flatFppfStructureSheafIso X)).toAdjunction)

/-- Module pullback along the restricted ringed morphism preserves finite limits. -/
theorem flatFppfRingedToposHom.modulePullback_preservesFiniteLimits (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u,
      (flatFppfInclusion X).op.HasPointwiseRightKanExtension P]
    [(flatFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [HasSheafify (inheritedFppfTopology X) (Type u)] :
    PreservesFiniteLimits (flatFppfModulePullback X) := sorry

/-- Module pullback along the restricted ringed morphism preserves finite colimits. -/
theorem flatFppfRingedToposHom.modulePullback_preservesFiniteColimits (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u,
      (flatFppfInclusion X).op.HasPointwiseRightKanExtension P]
    [(flatFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [HasSheafify (inheritedFppfTopology X) (Type u)] :
    PreservesFiniteColimits (flatFppfModulePullback X) := sorry

end AlgebraicGeometry.AlgebraicStack
