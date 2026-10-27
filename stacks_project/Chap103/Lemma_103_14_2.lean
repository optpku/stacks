/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Sites.RingedSquare
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Sites.RingedMorphism
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Sites.Precoverage
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Sites.Ringed
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Cohomology.Restriction
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Sites.ModuleLowerShriek
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Parasitic
import StacksCheckRecall

/-! The lisse-étale and flat-fppf inclusions are fully faithful, continuous and
cocontinuous. Their induced (ringed) topoi morphisms have restriction inverse
image, left adjoints on sets and abelian groups, invertible adjunction maps,
and flat module pullback. The explicit sheafification, sheaf-composition and
Kan-extension hypotheses stand for the Stacks bounded-site size convention. -/

@[expose] public section
open AlgebraicGeometry AlgebraicGeometry.GroupoidsOver CategoryTheory
open CategoryTheory.Functor CategoryTheory.Limits
open RingedSite.Cocontinuous
open scoped MorphismOfTopoiIn
universe u
namespace AlgebraicGeometry.AlgebraicStack
variable {S : Scheme.{u}}

/- Lemma 103.14.2: the lisseEtale inclusion induces the morphism of topoi with restriction inverse image. -/
@[stacks 0788] #check (AlgebraicGeometry.AlgebraicStack.lisseEtaleToposHom :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ (Type u),
      (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P],
    MorphismOfTopoiIn.{u + 1, u + 1, u, u, u}
      X.etaleTopology (lisseEtaleTopology X))

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleRestrictionComparison :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [HasSheafify X.etaleTopology (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ (Type u),
      (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P],
    (lisseEtaleInclusion X).sheafPullbackCocontinuous (Type u)
        (lisseEtaleTopology X) X.etaleTopology ⟶
      (lisseEtaleInclusion X).sheafPushforwardContinuous (Type u)
        (lisseEtaleTopology X) X.etaleTopology)

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleInclusion_restriction_spec :
  ∀ (X : GroupoidsOver S)
    [AlgebraicStack X],
    (lisseEtaleInclusion X).sheafPushforwardContinuous (Type u)
          (lisseEtaleTopology X) X.etaleTopology ⋙
        sheafToPresheaf (lisseEtaleTopology X) (Type u) =
      sheafToPresheaf X.etaleTopology (Type u) ⋙
        (whiskeringLeft _ _ (Type u)).obj (lisseEtaleInclusion X).op)

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleLowerShriek :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify X.etaleTopology (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ (Type u),
      (lisseEtaleInclusion X).op.HasLeftKanExtension P],
    Sheaf (lisseEtaleTopology X) (Type u) ⥤ Sheaf X.etaleTopology (Type u))

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleLowerShriek.adjunction :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify X.etaleTopology (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ (Type u),
      (lisseEtaleInclusion X).op.HasLeftKanExtension P],
    lisseEtaleLowerShriek X ⊣
      (lisseEtaleInclusion X).sheafPushforwardContinuous (Type u)
        (lisseEtaleTopology X) X.etaleTopology)

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleSheafAdjunctionCocontinuous :
  ∀ (X : GroupoidsOver S)
    [AlgebraicStack X]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ (Type u),
      (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P],
    (lisseEtaleInclusion X).sheafPushforwardContinuous (Type u)
        (lisseEtaleTopology X) X.etaleTopology ⊣
      (lisseEtaleInclusion X).sheafPushforwardCocontinuous (Type u)
        (lisseEtaleTopology X) X.etaleTopology)

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleAbelianLowerShriek :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify X.etaleTopology AddCommGrpCat.{u}]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (lisseEtaleInclusion X).op.HasLeftKanExtension P],
    Sheaf (lisseEtaleTopology X) AddCommGrpCat.{u} ⥤
      Sheaf X.etaleTopology AddCommGrpCat.{u})

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleAbelianLowerShriek.adjunction :
  ∀ (X : GroupoidsOver S)
    [AlgebraicStack X]
    [HasSheafify X.etaleTopology AddCommGrpCat.{u}]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (lisseEtaleInclusion X).op.HasLeftKanExtension P],
    lisseEtaleAbelianLowerShriek X ⊣
      (lisseEtaleInclusion X).sheafPushforwardContinuous AddCommGrpCat.{u}
        (lisseEtaleTopology X) X.etaleTopology)

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

section
variable (X : GroupoidsOver S) [AlgebraicStack X]
variable [HasSheafify (lisseEtaleTopology X) (Type u)] [HasSheafify X.etaleTopology (Type u)]
variable [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ (Type u),
  (lisseEtaleInclusion X).op.HasPointwiseLeftKanExtension P]
variable [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ (Type u),
  (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P]
variable [HasSheafify (lisseEtaleTopology X) AddCommGrpCat.{u}] [HasSheafify X.etaleTopology AddCommGrpCat.{u}]
variable [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u},
  (lisseEtaleInclusion X).op.HasPointwiseLeftKanExtension P]
variable [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u},
  (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P]

#check (CategoryTheory.ObjectProperty.full_ι (isLisse X) : (lisseEtaleInclusion X).Full)

#check (CategoryTheory.ObjectProperty.faithful_ι (isLisse X) : (lisseEtaleInclusion X).Faithful)

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleInclusion.instIsContinuous X :
  (lisseEtaleInclusion X).IsContinuous (lisseEtaleTopology X) X.etaleTopology)

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleInclusion.instIsCocontinuous X :
  (lisseEtaleInclusion X).IsCocontinuous (lisseEtaleTopology X) X.etaleTopology)

#check (CategoryTheory.Functor.CocontinuousPullback.comparison.isIso.{u} (lisseEtaleInclusion X) (lisseEtaleTopology X) X.etaleTopology :
  IsIso (lisseEtaleRestrictionComparison X))

#check (CategoryTheory.Functor.morphismOfTopoiInOfCocontinuous_inverseImage (lisseEtaleInclusion X) (lisseEtaleTopology X) X.etaleTopology :
  (lisseEtaleToposHom X).inverseImage =
    (lisseEtaleInclusion X).sheafPullbackCocontinuous (Type u) (lisseEtaleTopology X) X.etaleTopology)

#check (CategoryTheory.Functor.morphismOfTopoiInOfCocontinuous_pushforward (lisseEtaleInclusion X) (lisseEtaleTopology X) X.etaleTopology :
  (lisseEtaleToposHom X).pushforward =
    (lisseEtaleInclusion X).sheafPushforwardCocontinuous (Type u) (lisseEtaleTopology X) X.etaleTopology)

#check (CategoryTheory.Functor.sheafAdjunctionCocontinuous_counit_app_isIso_of_fullyFaithful
  (lisseEtaleTopology X) X.etaleTopology (lisseEtaleInclusion X) : ∀ F : Sheaf (lisseEtaleTopology X) (Type u),
    IsIso ((lisseEtaleSheafAdjunctionCocontinuous X).counit.app F))

#check (CategoryTheory.Functor.sheafAdjunctionContinuous_unit_app_isIso_of_fullyFaithful
  (lisseEtaleTopology X) X.etaleTopology (lisseEtaleInclusion X) : ∀ F : Sheaf (lisseEtaleTopology X) (Type u),
    IsIso ((lisseEtaleLowerShriek.adjunction X).unit.app F))

#check (CategoryTheory.Functor.sheafAdjunctionContinuous_unit_app_isIso_of_fullyFaithful
  (lisseEtaleTopology X) X.etaleTopology (lisseEtaleInclusion X) : ∀ F : Sheaf (lisseEtaleTopology X) AddCommGrpCat.{u},
    IsIso ((lisseEtaleAbelianLowerShriek.adjunction X).unit.app F))
end

/- Lemma 103.14.2: the flatFppf inclusion induces the morphism of topoi with restriction inverse image. -/
@[stacks 0788] #check (AlgebraicGeometry.AlgebraicStack.flatFppfToposHom :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ (Type u),
      (flatFppfInclusion X).op.HasPointwiseRightKanExtension P],
    MorphismOfTopoiIn.{u + 1, u + 1, u, u, u}
      (inheritedFppfTopology X) (flatFppfTopology X))

#check (AlgebraicGeometry.AlgebraicStack.flatFppfRestrictionComparison :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [HasSheafify (inheritedFppfTopology X) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ (Type u),
      (flatFppfInclusion X).op.HasPointwiseRightKanExtension P],
    (flatFppfInclusion X).sheafPullbackCocontinuous (Type u)
        (flatFppfTopology X) (inheritedFppfTopology X) ⟶
      (flatFppfInclusion X).sheafPushforwardContinuous (Type u)
        (flatFppfTopology X) (inheritedFppfTopology X))

#check (AlgebraicGeometry.AlgebraicStack.flatFppfInclusion_restriction_spec :
  ∀ (X : GroupoidsOver S)
    [AlgebraicStack X],
    (flatFppfInclusion X).sheafPushforwardContinuous (Type u)
          (flatFppfTopology X) (inheritedFppfTopology X) ⋙
        sheafToPresheaf (flatFppfTopology X) (Type u) =
      sheafToPresheaf (inheritedFppfTopology X) (Type u) ⋙
        (whiskeringLeft _ _ (Type u)).obj (flatFppfInclusion X).op)

#check (AlgebraicGeometry.AlgebraicStack.flatFppfLowerShriek :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (inheritedFppfTopology X) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ (Type u),
      (flatFppfInclusion X).op.HasLeftKanExtension P],
    Sheaf (flatFppfTopology X) (Type u) ⥤
      Sheaf (inheritedFppfTopology X) (Type u))

#check (AlgebraicGeometry.AlgebraicStack.flatFppfLowerShriek.adjunction :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (inheritedFppfTopology X) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ (Type u),
      (flatFppfInclusion X).op.HasLeftKanExtension P],
    flatFppfLowerShriek X ⊣
      (flatFppfInclusion X).sheafPushforwardContinuous (Type u)
        (flatFppfTopology X) (inheritedFppfTopology X))

#check (AlgebraicGeometry.AlgebraicStack.flatFppfSheafAdjunctionCocontinuous :
  ∀ (X : GroupoidsOver S)
    [AlgebraicStack X]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ (Type u),
      (flatFppfInclusion X).op.HasPointwiseRightKanExtension P],
    (flatFppfInclusion X).sheafPushforwardContinuous (Type u)
        (flatFppfTopology X) (inheritedFppfTopology X) ⊣
      (flatFppfInclusion X).sheafPushforwardCocontinuous (Type u)
        (flatFppfTopology X) (inheritedFppfTopology X))

#check (AlgebraicGeometry.AlgebraicStack.flatFppfAbelianLowerShriek :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (inheritedFppfTopology X) AddCommGrpCat.{u}]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (flatFppfInclusion X).op.HasLeftKanExtension P],
    Sheaf (flatFppfTopology X) AddCommGrpCat.{u} ⥤
      Sheaf (inheritedFppfTopology X) AddCommGrpCat.{u})

#check (AlgebraicGeometry.AlgebraicStack.flatFppfAbelianLowerShriek.adjunction :
  ∀ (X : GroupoidsOver S)
    [AlgebraicStack X]
    [HasSheafify (inheritedFppfTopology X) AddCommGrpCat.{u}]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (flatFppfInclusion X).op.HasLeftKanExtension P],
    flatFppfAbelianLowerShriek X ⊣
      (flatFppfInclusion X).sheafPushforwardContinuous AddCommGrpCat.{u}
        (flatFppfTopology X) (inheritedFppfTopology X))

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

section
variable (X : GroupoidsOver S) [AlgebraicStack X]
variable [HasSheafify (flatFppfTopology X) (Type u)] [HasSheafify (inheritedFppfTopology X) (Type u)]
variable [∀ P : (flatFppfSite X)ᵒᵖ ⥤ (Type u),
  (flatFppfInclusion X).op.HasPointwiseLeftKanExtension P]
variable [∀ P : (flatFppfSite X)ᵒᵖ ⥤ (Type u),
  (flatFppfInclusion X).op.HasPointwiseRightKanExtension P]
variable [HasSheafify (flatFppfTopology X) AddCommGrpCat.{u}] [HasSheafify (inheritedFppfTopology X) AddCommGrpCat.{u}]
variable [∀ P : (flatFppfSite X)ᵒᵖ ⥤ AddCommGrpCat.{u},
  (flatFppfInclusion X).op.HasPointwiseLeftKanExtension P]
variable [∀ P : (flatFppfSite X)ᵒᵖ ⥤ AddCommGrpCat.{u},
  (flatFppfInclusion X).op.HasPointwiseRightKanExtension P]

#check (CategoryTheory.ObjectProperty.full_ι (isFlat X) : (flatFppfInclusion X).Full)

#check (CategoryTheory.ObjectProperty.faithful_ι (isFlat X) : (flatFppfInclusion X).Faithful)

#check (AlgebraicGeometry.AlgebraicStack.flatFppfInclusion.instIsContinuous X :
  (flatFppfInclusion X).IsContinuous (flatFppfTopology X) (inheritedFppfTopology X))

#check (AlgebraicGeometry.AlgebraicStack.flatFppfInclusion.instIsCocontinuous X :
  (flatFppfInclusion X).IsCocontinuous (flatFppfTopology X) (inheritedFppfTopology X))

#check (CategoryTheory.Functor.CocontinuousPullback.comparison.isIso.{u} (flatFppfInclusion X) (flatFppfTopology X) (inheritedFppfTopology X) :
  IsIso (flatFppfRestrictionComparison X))

#check (CategoryTheory.Functor.morphismOfTopoiInOfCocontinuous_inverseImage (flatFppfInclusion X) (flatFppfTopology X) (inheritedFppfTopology X) :
  (flatFppfToposHom X).inverseImage =
    (flatFppfInclusion X).sheafPullbackCocontinuous (Type u) (flatFppfTopology X) (inheritedFppfTopology X))

#check (CategoryTheory.Functor.morphismOfTopoiInOfCocontinuous_pushforward (flatFppfInclusion X) (flatFppfTopology X) (inheritedFppfTopology X) :
  (flatFppfToposHom X).pushforward =
    (flatFppfInclusion X).sheafPushforwardCocontinuous (Type u) (flatFppfTopology X) (inheritedFppfTopology X))

#check (CategoryTheory.Functor.sheafAdjunctionCocontinuous_counit_app_isIso_of_fullyFaithful
  (flatFppfTopology X) (inheritedFppfTopology X) (flatFppfInclusion X) : ∀ F : Sheaf (flatFppfTopology X) (Type u),
    IsIso ((flatFppfSheafAdjunctionCocontinuous X).counit.app F))

#check (CategoryTheory.Functor.sheafAdjunctionContinuous_unit_app_isIso_of_fullyFaithful
  (flatFppfTopology X) (inheritedFppfTopology X) (flatFppfInclusion X) : ∀ F : Sheaf (flatFppfTopology X) (Type u),
    IsIso ((flatFppfLowerShriek.adjunction X).unit.app F))

#check (CategoryTheory.Functor.sheafAdjunctionContinuous_unit_app_isIso_of_fullyFaithful
  (flatFppfTopology X) (inheritedFppfTopology X) (flatFppfInclusion X) : ∀ F : Sheaf (flatFppfTopology X) AddCommGrpCat.{u},
    IsIso ((flatFppfAbelianLowerShriek.adjunction X).unit.app F))
end

end AlgebraicGeometry.AlgebraicStack
