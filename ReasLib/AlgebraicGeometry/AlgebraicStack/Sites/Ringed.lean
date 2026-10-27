/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import ReasLib.AlgebraicGeometry.RingedSite.Module.LowerShriek
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.HomOfCocontinuous
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

/-- The identity/restriction map of étale structure sheaves as ring presheaves. -/
def lisseEtaleStructurePresheafHom (X : GroupoidsOver S) [AlgebraicStack X] :
    (lisseEtaleInclusion X).op ⋙ (etaleStructureSheaf X).obj ⟶
      (lisseEtaleStructureSheaf X).obj :=
  ((lisseEtaleInclusion X).sheafPushforwardContinuousCompSheafToPresheafIso
      RingCat.{u} (lisseEtaleTopology X) X.etaleTopology).inv.app
    (etaleStructureSheaf X)

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

/-- The backward underlying sheaf map is the inverse restriction comparison followed by
 the inverse coefficient-forgetful comparison. -/
private abbrev lisseEtaleStructureSheafIsoInvUnderlying (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u,
      (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P]
    [(lisseEtaleTopology X).HasSheafCompose (forget RingCat.{u})]
    [X.etaleTopology.HasSheafCompose (forget RingCat.{u})]
    [HasSheafify X.etaleTopology (Type u)] :
    (sheafCompose (lisseEtaleTopology X) (forget RingCat.{u})).obj (lisseEtaleStructureSheaf X) ⟶
      (sheafCompose (lisseEtaleTopology X) (forget RingCat.{u})).obj
        ((lisseEtaleToposHom X).ringInverseImage.obj (etaleStructureSheaf X)) :=
  ((CocontinuousPullback.comparisonIso (lisseEtaleInclusion X) (lisseEtaleTopology X) X.etaleTopology).inv.app
      ((sheafCompose X.etaleTopology (forget RingCat.{u})).obj (etaleStructureSheaf X)) ≫
    (lisseEtaleToposHom X).ringInverseImageForgetIso.inv.app (etaleStructureSheaf X))

/-- The inverse comparison preserves one. -/
private theorem lisseEtaleStructureSheafIsoInv_map_one (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u,
      (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P]
    [(lisseEtaleTopology X).HasSheafCompose (forget RingCat.{u})]
    [X.etaleTopology.HasSheafCompose (forget RingCat.{u})]
    [HasSheafify X.etaleTopology (Type u)]
    (U : (lisseEtaleSite X)ᵒᵖ) :
    let source : RingCat.{u} := (lisseEtaleStructureSheaf X).obj.obj U
    let target : RingCat.{u} := ((lisseEtaleToposHom X).ringInverseImage.obj
      (etaleStructureSheaf X)).obj.obj U
    let backward : source → target := (lisseEtaleStructureSheafIsoInvUnderlying X).hom.app U
    backward (1 : source) = (1 : target) := sorry

/-- The inverse comparison preserves multiplication. -/
private theorem lisseEtaleStructureSheafIsoInv_map_mul (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u,
      (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P]
    [(lisseEtaleTopology X).HasSheafCompose (forget RingCat.{u})]
    [X.etaleTopology.HasSheafCompose (forget RingCat.{u})]
    [HasSheafify X.etaleTopology (Type u)]
    (U : (lisseEtaleSite X)ᵒᵖ) :
    let source : RingCat.{u} := (lisseEtaleStructureSheaf X).obj.obj U
    let target : RingCat.{u} := ((lisseEtaleToposHom X).ringInverseImage.obj
      (etaleStructureSheaf X)).obj.obj U
    let backward : source → target := (lisseEtaleStructureSheafIsoInvUnderlying X).hom.app U
    ∀ a b : source, backward (a * b) = (backward a : target) * backward b := sorry

/-- The inverse comparison preserves zero. -/
private theorem lisseEtaleStructureSheafIsoInv_map_zero (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u,
      (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P]
    [(lisseEtaleTopology X).HasSheafCompose (forget RingCat.{u})]
    [X.etaleTopology.HasSheafCompose (forget RingCat.{u})]
    [HasSheafify X.etaleTopology (Type u)]
    (U : (lisseEtaleSite X)ᵒᵖ) :
    let source : RingCat.{u} := (lisseEtaleStructureSheaf X).obj.obj U
    let target : RingCat.{u} := ((lisseEtaleToposHom X).ringInverseImage.obj
      (etaleStructureSheaf X)).obj.obj U
    let backward : source → target := (lisseEtaleStructureSheafIsoInvUnderlying X).hom.app U
    backward (0 : source) = (0 : target) := sorry

/-- The inverse comparison preserves addition. -/
private theorem lisseEtaleStructureSheafIsoInv_map_add (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u,
      (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P]
    [(lisseEtaleTopology X).HasSheafCompose (forget RingCat.{u})]
    [X.etaleTopology.HasSheafCompose (forget RingCat.{u})]
    [HasSheafify X.etaleTopology (Type u)]
    (U : (lisseEtaleSite X)ᵒᵖ) :
    let source : RingCat.{u} := (lisseEtaleStructureSheaf X).obj.obj U
    let target : RingCat.{u} := ((lisseEtaleToposHom X).ringInverseImage.obj
      (etaleStructureSheaf X)).obj.obj U
    let backward : source → target := (lisseEtaleStructureSheafIsoInvUnderlying X).hom.app U
    ∀ a b : source, backward (a + b) = (backward a : target) + backward b := sorry

/-- The inverse restriction function bundled as a sectionwise ring map. -/
private def lisseEtaleStructureSheafIsoInvApp (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u,
      (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P]
    [(lisseEtaleTopology X).HasSheafCompose (forget RingCat.{u})]
    [X.etaleTopology.HasSheafCompose (forget RingCat.{u})]
    [HasSheafify X.etaleTopology (Type u)] (U : (lisseEtaleSite X)ᵒᵖ) :
    (lisseEtaleStructureSheaf X).obj.obj U ⟶
      ((lisseEtaleToposHom X).ringInverseImage.obj (etaleStructureSheaf X)).obj.obj U :=
  let source : RingCat.{u} := (lisseEtaleStructureSheaf X).obj.obj U
  let target : RingCat.{u} := ((lisseEtaleToposHom X).ringInverseImage.obj
    (etaleStructureSheaf X)).obj.obj U
  @RingCat.ofHom source target source.ring target.ring
    { toFun := (lisseEtaleStructureSheafIsoInvUnderlying X).hom.app U
      map_one' := lisseEtaleStructureSheafIsoInv_map_one X U
      map_mul' := lisseEtaleStructureSheafIsoInv_map_mul X U
      map_zero' := lisseEtaleStructureSheafIsoInv_map_zero X U
      map_add' := lisseEtaleStructureSheafIsoInv_map_add X U }

/-- The inverse comparison commutes with restriction of sections. -/
private theorem lisseEtaleStructureSheafIsoInv_naturality (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u,
      (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P]
    [(lisseEtaleTopology X).HasSheafCompose (forget RingCat.{u})]
    [X.etaleTopology.HasSheafCompose (forget RingCat.{u})]
    [HasSheafify X.etaleTopology (Type u)]
    {U V : (lisseEtaleSite X)ᵒᵖ} (f : U ⟶ V) :
    (lisseEtaleStructureSheaf X).obj.map f ≫ lisseEtaleStructureSheafIsoInvApp X V =
      lisseEtaleStructureSheafIsoInvApp X U ≫
        ((lisseEtaleToposHom X).ringInverseImage.obj (etaleStructureSheaf X)).obj.map f := sorry

/-- The inverse of the structure-sheaf comparison, with its canonical section functions. -/
def lisseEtaleStructureSheafIsoInv (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u,
      (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P]
    [(lisseEtaleTopology X).HasSheafCompose (forget RingCat.{u})]
    [X.etaleTopology.HasSheafCompose (forget RingCat.{u})]
    [HasSheafify X.etaleTopology (Type u)] :
    lisseEtaleStructureSheaf X ⟶ (lisseEtaleToposHom X).ringInverseImage.obj (etaleStructureSheaf X) where
  hom :=
    { app := lisseEtaleStructureSheafIsoInvApp X
      naturality := fun _ _ f ↦ lisseEtaleStructureSheafIsoInv_naturality X f }

/-- The structure map followed by the inverse comparison is the identity. -/
private theorem lisseEtaleStructureSheafIso_hom_inv_id (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u,
      (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P]
    [(lisseEtaleTopology X).HasSheafCompose (forget RingCat.{u})]
    [X.etaleTopology.HasSheafCompose (forget RingCat.{u})]
    [HasSheafify X.etaleTopology (Type u)] :
    (lisseEtaleRingedToposHom X).structureMap ≫ lisseEtaleStructureSheafIsoInv X = 𝟙 _ := sorry

/-- The inverse comparison followed by the structure map is the identity. -/
private theorem lisseEtaleStructureSheafIso_inv_hom_id (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u,
      (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P]
    [(lisseEtaleTopology X).HasSheafCompose (forget RingCat.{u})]
    [X.etaleTopology.HasSheafCompose (forget RingCat.{u})]
    [HasSheafify X.etaleTopology (Type u)] :
    lisseEtaleStructureSheafIsoInv X ≫ (lisseEtaleRingedToposHom X).structureMap = 𝟙 _ := sorry

/-- The inverse-image ambient structure sheaf is canonically isomorphic to its restriction. -/
def lisseEtaleStructureSheafIso (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u,
      (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P]
    [(lisseEtaleTopology X).HasSheafCompose (forget RingCat.{u})]
    [X.etaleTopology.HasSheafCompose (forget RingCat.{u})]
    [HasSheafify X.etaleTopology (Type u)] :
    (lisseEtaleToposHom X).ringInverseImage.obj (etaleStructureSheaf X) ≅ lisseEtaleStructureSheaf X where
  hom := (lisseEtaleRingedToposHom X).structureMap
  inv := lisseEtaleStructureSheafIsoInv X
  hom_inv_id := lisseEtaleStructureSheafIso_hom_inv_id X
  inv_hom_id := lisseEtaleStructureSheafIso_inv_hom_id X

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

/-- The identity/restriction map of fppf structure sheaves as ring presheaves. -/
def flatFppfStructurePresheafHom (X : GroupoidsOver S) [AlgebraicStack X] :
    (flatFppfInclusion X).op ⋙ (structureSheaf X).obj ⟶
      (flatFppfStructureSheaf X).obj :=
  ((flatFppfInclusion X).sheafPushforwardContinuousCompSheafToPresheafIso
      RingCat.{u} (flatFppfTopology X) (inheritedFppfTopology X)).inv.app
    (structureSheaf X)

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

/-- The backward underlying sheaf map is the inverse restriction comparison followed by
 the inverse coefficient-forgetful comparison. -/
private abbrev flatFppfStructureSheafIsoInvUnderlying (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u,
      (flatFppfInclusion X).op.HasPointwiseRightKanExtension P]
    [(flatFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [HasSheafify (inheritedFppfTopology X) (Type u)] :
    (sheafCompose (flatFppfTopology X) (forget RingCat.{u})).obj (flatFppfStructureSheaf X) ⟶
      (sheafCompose (flatFppfTopology X) (forget RingCat.{u})).obj
        ((flatFppfToposHom X).ringInverseImage.obj (structureSheaf X)) :=
  ((CocontinuousPullback.comparisonIso (flatFppfInclusion X) (flatFppfTopology X) (inheritedFppfTopology X)).inv.app
      ((sheafCompose (inheritedFppfTopology X) (forget RingCat.{u})).obj (structureSheaf X)) ≫
    (flatFppfToposHom X).ringInverseImageForgetIso.inv.app (structureSheaf X))

/-- The inverse comparison preserves one. -/
private theorem flatFppfStructureSheafIsoInv_map_one (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u,
      (flatFppfInclusion X).op.HasPointwiseRightKanExtension P]
    [(flatFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [HasSheafify (inheritedFppfTopology X) (Type u)]
    (U : (flatFppfSite X)ᵒᵖ) :
    let source : RingCat.{u} := (flatFppfStructureSheaf X).obj.obj U
    let target : RingCat.{u} := ((flatFppfToposHom X).ringInverseImage.obj
      (structureSheaf X)).obj.obj U
    let backward : source → target := (flatFppfStructureSheafIsoInvUnderlying X).hom.app U
    backward (1 : source) = (1 : target) := sorry

/-- The inverse comparison preserves multiplication. -/
private theorem flatFppfStructureSheafIsoInv_map_mul (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u,
      (flatFppfInclusion X).op.HasPointwiseRightKanExtension P]
    [(flatFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [HasSheafify (inheritedFppfTopology X) (Type u)]
    (U : (flatFppfSite X)ᵒᵖ) :
    let source : RingCat.{u} := (flatFppfStructureSheaf X).obj.obj U
    let target : RingCat.{u} := ((flatFppfToposHom X).ringInverseImage.obj
      (structureSheaf X)).obj.obj U
    let backward : source → target := (flatFppfStructureSheafIsoInvUnderlying X).hom.app U
    ∀ a b : source, backward (a * b) = (backward a : target) * backward b := sorry

/-- The inverse comparison preserves zero. -/
private theorem flatFppfStructureSheafIsoInv_map_zero (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u,
      (flatFppfInclusion X).op.HasPointwiseRightKanExtension P]
    [(flatFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [HasSheafify (inheritedFppfTopology X) (Type u)]
    (U : (flatFppfSite X)ᵒᵖ) :
    let source : RingCat.{u} := (flatFppfStructureSheaf X).obj.obj U
    let target : RingCat.{u} := ((flatFppfToposHom X).ringInverseImage.obj
      (structureSheaf X)).obj.obj U
    let backward : source → target := (flatFppfStructureSheafIsoInvUnderlying X).hom.app U
    backward (0 : source) = (0 : target) := sorry

/-- The inverse comparison preserves addition. -/
private theorem flatFppfStructureSheafIsoInv_map_add (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u,
      (flatFppfInclusion X).op.HasPointwiseRightKanExtension P]
    [(flatFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [HasSheafify (inheritedFppfTopology X) (Type u)]
    (U : (flatFppfSite X)ᵒᵖ) :
    let source : RingCat.{u} := (flatFppfStructureSheaf X).obj.obj U
    let target : RingCat.{u} := ((flatFppfToposHom X).ringInverseImage.obj
      (structureSheaf X)).obj.obj U
    let backward : source → target := (flatFppfStructureSheafIsoInvUnderlying X).hom.app U
    ∀ a b : source, backward (a + b) = (backward a : target) + backward b := sorry

/-- The inverse restriction function bundled as a sectionwise ring map. -/
private def flatFppfStructureSheafIsoInvApp (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u,
      (flatFppfInclusion X).op.HasPointwiseRightKanExtension P]
    [(flatFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [HasSheafify (inheritedFppfTopology X) (Type u)] (U : (flatFppfSite X)ᵒᵖ) :
    (flatFppfStructureSheaf X).obj.obj U ⟶
      ((flatFppfToposHom X).ringInverseImage.obj (structureSheaf X)).obj.obj U :=
  let source : RingCat.{u} := (flatFppfStructureSheaf X).obj.obj U
  let target : RingCat.{u} := ((flatFppfToposHom X).ringInverseImage.obj
    (structureSheaf X)).obj.obj U
  @RingCat.ofHom source target source.ring target.ring
    { toFun := (flatFppfStructureSheafIsoInvUnderlying X).hom.app U
      map_one' := flatFppfStructureSheafIsoInv_map_one X U
      map_mul' := flatFppfStructureSheafIsoInv_map_mul X U
      map_zero' := flatFppfStructureSheafIsoInv_map_zero X U
      map_add' := flatFppfStructureSheafIsoInv_map_add X U }

/-- The inverse comparison commutes with restriction of sections. -/
private theorem flatFppfStructureSheafIsoInv_naturality (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u,
      (flatFppfInclusion X).op.HasPointwiseRightKanExtension P]
    [(flatFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [HasSheafify (inheritedFppfTopology X) (Type u)]
    {U V : (flatFppfSite X)ᵒᵖ} (f : U ⟶ V) :
    (flatFppfStructureSheaf X).obj.map f ≫ flatFppfStructureSheafIsoInvApp X V =
      flatFppfStructureSheafIsoInvApp X U ≫
        ((flatFppfToposHom X).ringInverseImage.obj (structureSheaf X)).obj.map f := sorry

/-- The inverse of the structure-sheaf comparison, with its canonical section functions. -/
def flatFppfStructureSheafIsoInv (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u,
      (flatFppfInclusion X).op.HasPointwiseRightKanExtension P]
    [(flatFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [HasSheafify (inheritedFppfTopology X) (Type u)] :
    flatFppfStructureSheaf X ⟶ (flatFppfToposHom X).ringInverseImage.obj (structureSheaf X) where
  hom :=
    { app := flatFppfStructureSheafIsoInvApp X
      naturality := fun _ _ f ↦ flatFppfStructureSheafIsoInv_naturality X f }

/-- The structure map followed by the inverse comparison is the identity. -/
private theorem flatFppfStructureSheafIso_hom_inv_id (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u,
      (flatFppfInclusion X).op.HasPointwiseRightKanExtension P]
    [(flatFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [HasSheafify (inheritedFppfTopology X) (Type u)] :
    (flatFppfRingedToposHom X).structureMap ≫ flatFppfStructureSheafIsoInv X = 𝟙 _ := sorry

/-- The inverse comparison followed by the structure map is the identity. -/
private theorem flatFppfStructureSheafIso_inv_hom_id (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u,
      (flatFppfInclusion X).op.HasPointwiseRightKanExtension P]
    [(flatFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [HasSheafify (inheritedFppfTopology X) (Type u)] :
    flatFppfStructureSheafIsoInv X ≫ (flatFppfRingedToposHom X).structureMap = 𝟙 _ := sorry

/-- The inverse-image ambient structure sheaf is canonically isomorphic to its restriction. -/
def flatFppfStructureSheafIso (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u,
      (flatFppfInclusion X).op.HasPointwiseRightKanExtension P]
    [(flatFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [HasSheafify (inheritedFppfTopology X) (Type u)] :
    (flatFppfToposHom X).ringInverseImage.obj (structureSheaf X) ≅ flatFppfStructureSheaf X where
  hom := (flatFppfRingedToposHom X).structureMap
  inv := flatFppfStructureSheafIsoInv X
  hom_inv_id := flatFppfStructureSheafIso_hom_inv_id X
  inv_hom_id := flatFppfStructureSheafIso_inv_hom_id X

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
