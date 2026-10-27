/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Sites.Precoverage
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Sites.Ringed

/-! Compatibility checks for Lemma 103.14.2. The explicit sheafification,
sheaf-composition and Kan-extension premises stand for the Stacks bounded-site
size convention. -/

@[expose] public section
open AlgebraicGeometry AlgebraicGeometry.GroupoidsOver CategoryTheory
open CategoryTheory.Functor CategoryTheory.Limits
open RingedSite.Cocontinuous
open scoped MorphismOfTopoiIn
universe u
namespace AlgebraicGeometry.AlgebraicStack
variable {S : Scheme.{u}}

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleStructureSheaf :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X],
    Sheaf (lisseEtaleTopology X) RingCat.{u})

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleStructureSheaf_eq :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X],
    lisseEtaleStructureSheaf X =
      ((lisseEtaleInclusion X).sheafPushforwardContinuous RingCat.{u}
        (lisseEtaleTopology X) X.etaleTopology).obj (etaleStructureSheaf X))

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleRingedSite :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X],
    RingedSite.{u + 1, u, u})

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleRingedSite_structureSheaf :
  ∀ (X : GroupoidsOver S)
    [AlgebraicStack X],
    (lisseEtaleRingedSite X).structureSheaf = lisseEtaleStructureSheaf X)

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleStructurePresheafHom :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X],
    (lisseEtaleInclusion X).op ⋙ (etaleStructureSheaf X).obj ⟶
      (lisseEtaleStructureSheaf X).obj)

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleStructurePresheafHom_eq :
  ∀ (X : GroupoidsOver S)
    [AlgebraicStack X],
    lisseEtaleStructurePresheafHom X =
      ((lisseEtaleInclusion X).sheafPushforwardContinuousCompSheafToPresheafIso
          RingCat.{u} (lisseEtaleTopology X) X.etaleTopology).inv.app
        (etaleStructureSheaf X))

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleRingedToposHom :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u,
      (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P]
    [(lisseEtaleTopology X).HasSheafCompose (forget RingCat.{u})]
    [X.etaleTopology.HasSheafCompose (forget RingCat.{u})],
    RingedSite.ToposHom (lisseEtaleRingedSite X) (etaleRingedSite X))

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleRingedToposHom_toTopos :
  ∀ (X : GroupoidsOver S)
    [AlgebraicStack X]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u,
      (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P]
    [(lisseEtaleTopology X).HasSheafCompose (forget RingCat.{u})]
    [X.etaleTopology.HasSheafCompose (forget RingCat.{u})],
    (lisseEtaleRingedToposHom X).toTopos = lisseEtaleToposHom X)

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleStructureSheafIsoInv :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u,
      (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P]
    [(lisseEtaleTopology X).HasSheafCompose (forget RingCat.{u})]
    [X.etaleTopology.HasSheafCompose (forget RingCat.{u})]
    [HasSheafify X.etaleTopology (Type u)],
    lisseEtaleStructureSheaf X ⟶ (lisseEtaleToposHom X).ringInverseImage.obj (etaleStructureSheaf X))

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleStructureSheafIso :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u,
      (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P]
    [(lisseEtaleTopology X).HasSheafCompose (forget RingCat.{u})]
    [X.etaleTopology.HasSheafCompose (forget RingCat.{u})]
    [HasSheafify X.etaleTopology (Type u)],
    (lisseEtaleToposHom X).ringInverseImage.obj (etaleStructureSheaf X) ≅ lisseEtaleStructureSheaf X)

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleRingedToposHom.structureMap_isIso :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u,
      (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P]
    [(lisseEtaleTopology X).HasSheafCompose (forget RingCat.{u})]
    [X.etaleTopology.HasSheafCompose (forget RingCat.{u})]
    [HasSheafify X.etaleTopology (Type u)],
    IsIso (lisseEtaleRingedToposHom X).structureMap)

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleRingedToposHom.restrictScalars_isRightAdjoint :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u,
      (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P]
    [(lisseEtaleTopology X).HasSheafCompose (forget RingCat.{u})]
    [X.etaleTopology.HasSheafCompose (forget RingCat.{u})]
    [HasSheafify X.etaleTopology (Type u)],
    (SheafOfModules.restrictScalars.{u} (lisseEtaleRingedToposHom X).structureMap).IsRightAdjoint)

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleModulePullback :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u,
      (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P]
    [(lisseEtaleTopology X).HasSheafCompose (forget RingCat.{u})]
    [X.etaleTopology.HasSheafCompose (forget RingCat.{u})]
    [HasSheafify X.etaleTopology (Type u)],
    SheafOfModules.{u} (etaleRingedSite X).structureSheaf ⥤
      SheafOfModules.{u} (lisseEtaleStructureSheaf X))

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleRingedToposHom_modulePullback_eq :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u,
      (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P]
    [(lisseEtaleTopology X).HasSheafCompose (forget RingCat.{u})]
    [X.etaleTopology.HasSheafCompose (forget RingCat.{u})]
    [HasSheafify X.etaleTopology (Type u)],
    lisseEtaleModulePullback X =
      (lisseEtaleToposHom X).moduleInverseImage (etaleStructureSheaf X) ⋙
        @SheafOfModules.ChangeOfRings.extendScalars _ _ _ _ _
          (lisseEtaleRingedToposHom X).structureMap
          (lisseEtaleRingedToposHom.restrictScalars_isRightAdjoint X))

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleModulePullbackRestrictionIso :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u,
      (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P]
    [(lisseEtaleTopology X).HasSheafCompose (forget RingCat.{u})]
    [X.etaleTopology.HasSheafCompose (forget RingCat.{u})]
    [HasSheafify X.etaleTopology (Type u)],
    lisseEtaleModulePullback X ≅
      (lisseEtaleToposHom X).moduleInverseImage (etaleStructureSheaf X) ⋙
        SheafOfModules.restrictScalars.{u} (lisseEtaleStructureSheafIso X).inv)

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleRingedToposHom.modulePullback_preservesFiniteLimits :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u,
      (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P]
    [(lisseEtaleTopology X).HasSheafCompose (forget RingCat.{u})]
    [X.etaleTopology.HasSheafCompose (forget RingCat.{u})]
    [HasSheafify X.etaleTopology (Type u)],
    PreservesFiniteLimits (lisseEtaleModulePullback X))

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleRingedToposHom.modulePullback_preservesFiniteColimits :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u,
      (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P]
    [(lisseEtaleTopology X).HasSheafCompose (forget RingCat.{u})]
    [X.etaleTopology.HasSheafCompose (forget RingCat.{u})]
    [HasSheafify X.etaleTopology (Type u)],
    PreservesFiniteColimits (lisseEtaleModulePullback X))

#check (AlgebraicGeometry.AlgebraicStack.flatFppfStructureSheaf :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X],
    Sheaf (flatFppfTopology X) RingCat.{u})

#check (AlgebraicGeometry.AlgebraicStack.flatFppfStructureSheaf_eq :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X],
    flatFppfStructureSheaf X =
      ((flatFppfInclusion X).sheafPushforwardContinuous RingCat.{u}
        (flatFppfTopology X) (inheritedFppfTopology X)).obj (structureSheaf X))

#check (AlgebraicGeometry.AlgebraicStack.flatFppfRingedSite :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X],
    RingedSite.{u + 1, u, u})

#check (AlgebraicGeometry.AlgebraicStack.flatFppfRingedSite_structureSheaf :
  ∀ (X : GroupoidsOver S)
    [AlgebraicStack X],
    (flatFppfRingedSite X).structureSheaf = flatFppfStructureSheaf X)

#check (AlgebraicGeometry.AlgebraicStack.flatFppfStructurePresheafHom :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X],
    (flatFppfInclusion X).op ⋙ (structureSheaf X).obj ⟶
      (flatFppfStructureSheaf X).obj)

#check (AlgebraicGeometry.AlgebraicStack.flatFppfStructurePresheafHom_eq :
  ∀ (X : GroupoidsOver S)
    [AlgebraicStack X],
    flatFppfStructurePresheafHom X =
      ((flatFppfInclusion X).sheafPushforwardContinuousCompSheafToPresheafIso
          RingCat.{u} (flatFppfTopology X) (inheritedFppfTopology X)).inv.app
        (structureSheaf X))

#check (AlgebraicGeometry.AlgebraicStack.flatFppfRingedToposHom :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u,
      (flatFppfInclusion X).op.HasPointwiseRightKanExtension P]
    [(flatFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology X).HasSheafCompose (forget RingCat.{u})],
    RingedSite.ToposHom (flatFppfRingedSite X) (ringedSite X))

#check (AlgebraicGeometry.AlgebraicStack.flatFppfRingedToposHom_toTopos :
  ∀ (X : GroupoidsOver S)
    [AlgebraicStack X]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u,
      (flatFppfInclusion X).op.HasPointwiseRightKanExtension P]
    [(flatFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology X).HasSheafCompose (forget RingCat.{u})],
    (flatFppfRingedToposHom X).toTopos = flatFppfToposHom X)

#check (AlgebraicGeometry.AlgebraicStack.flatFppfStructureSheafIsoInv :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u,
      (flatFppfInclusion X).op.HasPointwiseRightKanExtension P]
    [(flatFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [HasSheafify (inheritedFppfTopology X) (Type u)],
    flatFppfStructureSheaf X ⟶ (flatFppfToposHom X).ringInverseImage.obj (structureSheaf X))

#check (AlgebraicGeometry.AlgebraicStack.flatFppfStructureSheafIso :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u,
      (flatFppfInclusion X).op.HasPointwiseRightKanExtension P]
    [(flatFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [HasSheafify (inheritedFppfTopology X) (Type u)],
    (flatFppfToposHom X).ringInverseImage.obj (structureSheaf X) ≅ flatFppfStructureSheaf X)

#check (AlgebraicGeometry.AlgebraicStack.flatFppfRingedToposHom.structureMap_isIso :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u,
      (flatFppfInclusion X).op.HasPointwiseRightKanExtension P]
    [(flatFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [HasSheafify (inheritedFppfTopology X) (Type u)],
    IsIso (flatFppfRingedToposHom X).structureMap)

#check (AlgebraicGeometry.AlgebraicStack.flatFppfRingedToposHom.restrictScalars_isRightAdjoint :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u,
      (flatFppfInclusion X).op.HasPointwiseRightKanExtension P]
    [(flatFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [HasSheafify (inheritedFppfTopology X) (Type u)],
    (SheafOfModules.restrictScalars.{u} (flatFppfRingedToposHom X).structureMap).IsRightAdjoint)

#check (AlgebraicGeometry.AlgebraicStack.flatFppfModulePullback :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u,
      (flatFppfInclusion X).op.HasPointwiseRightKanExtension P]
    [(flatFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [HasSheafify (inheritedFppfTopology X) (Type u)],
    SheafOfModules.{u} (ringedSite X).structureSheaf ⥤
      SheafOfModules.{u} (flatFppfStructureSheaf X))

#check (AlgebraicGeometry.AlgebraicStack.flatFppfRingedToposHom_modulePullback_eq :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u,
      (flatFppfInclusion X).op.HasPointwiseRightKanExtension P]
    [(flatFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [HasSheafify (inheritedFppfTopology X) (Type u)],
    flatFppfModulePullback X =
      (flatFppfToposHom X).moduleInverseImage (structureSheaf X) ⋙
        @SheafOfModules.ChangeOfRings.extendScalars _ _ _ _ _
          (flatFppfRingedToposHom X).structureMap
          (flatFppfRingedToposHom.restrictScalars_isRightAdjoint X))

#check (AlgebraicGeometry.AlgebraicStack.flatFppfModulePullbackRestrictionIso :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u,
      (flatFppfInclusion X).op.HasPointwiseRightKanExtension P]
    [(flatFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [HasSheafify (inheritedFppfTopology X) (Type u)],
    flatFppfModulePullback X ≅
      (flatFppfToposHom X).moduleInverseImage (structureSheaf X) ⋙
        SheafOfModules.restrictScalars.{u} (flatFppfStructureSheafIso X).inv)

#check (AlgebraicGeometry.AlgebraicStack.flatFppfRingedToposHom.modulePullback_preservesFiniteLimits :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u,
      (flatFppfInclusion X).op.HasPointwiseRightKanExtension P]
    [(flatFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [HasSheafify (inheritedFppfTopology X) (Type u)],
    PreservesFiniteLimits (flatFppfModulePullback X))

#check (AlgebraicGeometry.AlgebraicStack.flatFppfRingedToposHom.modulePullback_preservesFiniteColimits :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u,
      (flatFppfInclusion X).op.HasPointwiseRightKanExtension P]
    [(flatFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [HasSheafify (inheritedFppfTopology X) (Type u)],
    PreservesFiniteColimits (flatFppfModulePullback X))

end AlgebraicGeometry.AlgebraicStack
