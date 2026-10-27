/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Sites.RingedSquare

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.GroupoidsOver CategoryTheory
open CategoryTheory.Functor
open FiberedCategoryOver.Groupoids
open RingedSite.ToposHom
open scoped Bicategory MorphismOfTopoiIn

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack Y]

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleBeckChevalleySquare :
  ∀ (f : X ⟶ Y) [Smooth f],
    CatCommSq (lisseEtaleInclusion X) (lisseEtaleMap f) (toFunctor f)
      (lisseEtaleInclusion Y))

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleBeckChevalleySquare_iso :
  ∀ (f : X ⟶ Y) [Smooth f],
    (lisseEtaleBeckChevalleySquare f).iso = (lisseEtaleMap_comp_ι f).symm)

#check (AlgebraicGeometry.AlgebraicStack.lisseEtalePushforwardRestrictionComparison :
  ∀ (f : X ⟶ Y) [Smooth f]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [HasSheafify X.etaleTopology (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleMap f).op.HasPointwiseRightKanExtension P],
    (toFunctor f).sheafPushforwardCocontinuous (Type u)
        X.etaleTopology Y.etaleTopology ⋙
      (lisseEtaleInclusion Y).sheafPushforwardContinuous (Type u)
        (lisseEtaleTopology Y) Y.etaleTopology ⟶
      (lisseEtaleInclusion X).sheafPushforwardContinuous (Type u)
        (lisseEtaleTopology X) X.etaleTopology ⋙
        (lisseEtaleMap f).sheafPushforwardCocontinuous (Type u)
          (lisseEtaleTopology X) (lisseEtaleTopology Y))

#check (AlgebraicGeometry.AlgebraicStack.lisseEtalePushforwardRestrictionComparison_eq :
  ∀ (f : X ⟶ Y) [Smooth f]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [HasSheafify X.etaleTopology (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleMap f).op.HasPointwiseRightKanExtension P],
    lisseEtalePushforwardRestrictionComparison f =
      CatCommSq.BeckChevalley.comparison.{u} (lisseEtaleTopology X) X.etaleTopology
        (lisseEtaleTopology Y) Y.etaleTopology (lisseEtaleBeckChevalleySquare f))

#check (AlgebraicGeometry.AlgebraicStack.lisseEtalePushforwardRestrictionComparison.instIsIso :
  ∀ (f : X ⟶ Y) [Smooth f]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [HasSheafify X.etaleTopology (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleMap f).op.HasPointwiseRightKanExtension P],
    IsIso (lisseEtalePushforwardRestrictionComparison f))

#check (AlgebraicGeometry.AlgebraicStack.lisseEtalePushforwardRestrictionIso :
  ∀ (f : X ⟶ Y) [Smooth f]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [HasSheafify X.etaleTopology (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleMap f).op.HasPointwiseRightKanExtension P],
    (lisseEtaleInclusion X).sheafPushforwardContinuous (Type u)
        (lisseEtaleTopology X) X.etaleTopology ⋙
      (lisseEtaleMap f).sheafPushforwardCocontinuous (Type u)
        (lisseEtaleTopology X) (lisseEtaleTopology Y) ≅
      (toFunctor f).sheafPushforwardCocontinuous (Type u)
        X.etaleTopology Y.etaleTopology ⋙
        (lisseEtaleInclusion Y).sheafPushforwardContinuous (Type u)
          (lisseEtaleTopology Y) Y.etaleTopology)

#check (AlgebraicGeometry.AlgebraicStack.lisseEtalePushforwardRestrictionIso_eq :
  ∀ (f : X ⟶ Y) [Smooth f]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [HasSheafify X.etaleTopology (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleMap f).op.HasPointwiseRightKanExtension P],
    lisseEtalePushforwardRestrictionIso f =
      (asIso (lisseEtalePushforwardRestrictionComparison f)).symm)

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleFunctorialSquare_homIso :
  ∀ (f : X ⟶ Y) [Smooth f]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [HasSheafify X.etaleTopology (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleMap f).op.HasPointwiseRightKanExtension P]
    [HasSheafify (lisseEtaleTopology Y) (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P]
    [∀ P : (lisseEtaleSite Y)ᵒᵖ ⥤ Type u, (lisseEtaleInclusion Y).op.HasPointwiseRightKanExtension P]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleMap f ⋙ lisseEtaleInclusion Y).op.HasPointwiseRightKanExtension P]
    [(lisseEtaleTopology X).HasSheafCompose (forget RingCat.{u})]
    [X.etaleTopology.HasSheafCompose (forget RingCat.{u})]
    [(lisseEtaleTopology Y).HasSheafCompose (forget RingCat.{u})]
    [Y.etaleTopology.HasSheafCompose (forget RingCat.{u})],
    (comp (lisseEtaleRingedToposHom X) (toFunctor.etaleRingedToposHom f)).toTopos.pushforward ≅
      (comp (lisseEtaleMap.ringedToposHom f) (lisseEtaleRingedToposHom Y)).toTopos.pushforward)

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleFunctorialSquare_homIso_eq :
  ∀ (f : X ⟶ Y) [Smooth f]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [HasSheafify X.etaleTopology (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleMap f).op.HasPointwiseRightKanExtension P]
    [HasSheafify (lisseEtaleTopology Y) (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P]
    [∀ P : (lisseEtaleSite Y)ᵒᵖ ⥤ Type u, (lisseEtaleInclusion Y).op.HasPointwiseRightKanExtension P]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleMap f ⋙ lisseEtaleInclusion Y).op.HasPointwiseRightKanExtension P]
    [(lisseEtaleTopology X).HasSheafCompose (forget RingCat.{u})]
    [X.etaleTopology.HasSheafCompose (forget RingCat.{u})]
    [(lisseEtaleTopology Y).HasSheafCompose (forget RingCat.{u})]
    [Y.etaleTopology.HasSheafCompose (forget RingCat.{u})],
    lisseEtaleFunctorialSquare_homIso f =
      sheafPushforwardCocontinuousComp' (lisseEtaleTopology X) X.etaleTopology
          Y.etaleTopology (lisseEtaleInclusion X) (toFunctor f)
          (lisseEtaleMap_comp_ι f).symm ≪≫
        (sheafPushforwardCocontinuousComp (lisseEtaleTopology X)
          (lisseEtaleTopology Y) Y.etaleTopology (lisseEtaleMap f)
          (lisseEtaleInclusion Y)).symm)

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleFunctorialSquare_homIso_comm :
  ∀ (f : X ⟶ Y) [Smooth f]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [HasSheafify X.etaleTopology (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleMap f).op.HasPointwiseRightKanExtension P]
    [HasSheafify (lisseEtaleTopology Y) (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P]
    [∀ P : (lisseEtaleSite Y)ᵒᵖ ⥤ Type u, (lisseEtaleInclusion Y).op.HasPointwiseRightKanExtension P]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleMap f ⋙ lisseEtaleInclusion Y).op.HasPointwiseRightKanExtension P]
    [(lisseEtaleTopology X).HasSheafCompose (forget RingCat.{u})]
    [X.etaleTopology.HasSheafCompose (forget RingCat.{u})]
    [(lisseEtaleTopology Y).HasSheafCompose (forget RingCat.{u})]
    [Y.etaleTopology.HasSheafCompose (forget RingCat.{u})],
    (comp (lisseEtaleRingedToposHom X)
          (toFunctor.etaleRingedToposHom f)).directStructureMap ≫
        (MorphismOfTopoiIn.ringDirectImageNatTrans
          (lisseEtaleFunctorialSquare_homIso f).hom).app
          (lisseEtaleRingedSite X).structureSheaf =
      (comp (lisseEtaleMap.ringedToposHom f)
        (lisseEtaleRingedToposHom Y)).directStructureMap)

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleFunctorialSquare :
  ∀ (f : X ⟶ Y) [Smooth f]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [HasSheafify X.etaleTopology (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleMap f).op.HasPointwiseRightKanExtension P]
    [HasSheafify (lisseEtaleTopology Y) (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P]
    [∀ P : (lisseEtaleSite Y)ᵒᵖ ⥤ Type u, (lisseEtaleInclusion Y).op.HasPointwiseRightKanExtension P]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleMap f ⋙ lisseEtaleInclusion Y).op.HasPointwiseRightKanExtension P]
    [(lisseEtaleTopology X).HasSheafCompose (forget RingCat.{u})]
    [X.etaleTopology.HasSheafCompose (forget RingCat.{u})]
    [(lisseEtaleTopology Y).HasSheafCompose (forget RingCat.{u})]
    [Y.etaleTopology.HasSheafCompose (forget RingCat.{u})],
    CommSquare (lisseEtaleRingedSite X) (etaleRingedSite X)
      (lisseEtaleRingedSite Y) (etaleRingedSite Y))

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleFunctorialSquare_upper :
  ∀ (f : X ⟶ Y) [Smooth f]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [HasSheafify X.etaleTopology (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleMap f).op.HasPointwiseRightKanExtension P]
    [HasSheafify (lisseEtaleTopology Y) (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P]
    [∀ P : (lisseEtaleSite Y)ᵒᵖ ⥤ Type u, (lisseEtaleInclusion Y).op.HasPointwiseRightKanExtension P]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleMap f ⋙ lisseEtaleInclusion Y).op.HasPointwiseRightKanExtension P]
    [(lisseEtaleTopology X).HasSheafCompose (forget RingCat.{u})]
    [X.etaleTopology.HasSheafCompose (forget RingCat.{u})]
    [(lisseEtaleTopology Y).HasSheafCompose (forget RingCat.{u})]
    [Y.etaleTopology.HasSheafCompose (forget RingCat.{u})],
    (lisseEtaleFunctorialSquare f).upper = lisseEtaleRingedToposHom X)

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleFunctorialSquare_left :
  ∀ (f : X ⟶ Y) [Smooth f]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [HasSheafify X.etaleTopology (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleMap f).op.HasPointwiseRightKanExtension P]
    [HasSheafify (lisseEtaleTopology Y) (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P]
    [∀ P : (lisseEtaleSite Y)ᵒᵖ ⥤ Type u, (lisseEtaleInclusion Y).op.HasPointwiseRightKanExtension P]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleMap f ⋙ lisseEtaleInclusion Y).op.HasPointwiseRightKanExtension P]
    [(lisseEtaleTopology X).HasSheafCompose (forget RingCat.{u})]
    [X.etaleTopology.HasSheafCompose (forget RingCat.{u})]
    [(lisseEtaleTopology Y).HasSheafCompose (forget RingCat.{u})]
    [Y.etaleTopology.HasSheafCompose (forget RingCat.{u})],
    (lisseEtaleFunctorialSquare f).left = lisseEtaleMap.ringedToposHom f)

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleFunctorialSquare_right :
  ∀ (f : X ⟶ Y) [Smooth f]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [HasSheafify X.etaleTopology (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleMap f).op.HasPointwiseRightKanExtension P]
    [HasSheafify (lisseEtaleTopology Y) (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P]
    [∀ P : (lisseEtaleSite Y)ᵒᵖ ⥤ Type u, (lisseEtaleInclusion Y).op.HasPointwiseRightKanExtension P]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleMap f ⋙ lisseEtaleInclusion Y).op.HasPointwiseRightKanExtension P]
    [(lisseEtaleTopology X).HasSheafCompose (forget RingCat.{u})]
    [X.etaleTopology.HasSheafCompose (forget RingCat.{u})]
    [(lisseEtaleTopology Y).HasSheafCompose (forget RingCat.{u})]
    [Y.etaleTopology.HasSheafCompose (forget RingCat.{u})],
    (lisseEtaleFunctorialSquare f).right = toFunctor.etaleRingedToposHom f)

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleFunctorialSquare_lower :
  ∀ (f : X ⟶ Y) [Smooth f]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [HasSheafify X.etaleTopology (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleMap f).op.HasPointwiseRightKanExtension P]
    [HasSheafify (lisseEtaleTopology Y) (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P]
    [∀ P : (lisseEtaleSite Y)ᵒᵖ ⥤ Type u, (lisseEtaleInclusion Y).op.HasPointwiseRightKanExtension P]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleMap f ⋙ lisseEtaleInclusion Y).op.HasPointwiseRightKanExtension P]
    [(lisseEtaleTopology X).HasSheafCompose (forget RingCat.{u})]
    [X.etaleTopology.HasSheafCompose (forget RingCat.{u})]
    [(lisseEtaleTopology Y).HasSheafCompose (forget RingCat.{u})]
    [Y.etaleTopology.HasSheafCompose (forget RingCat.{u})],
    (lisseEtaleFunctorialSquare f).lower = lisseEtaleRingedToposHom Y)

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleFunctorialSquare_homIso_eq_cell :
  ∀ (f : X ⟶ Y) [Smooth f]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [HasSheafify X.etaleTopology (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleMap f).op.HasPointwiseRightKanExtension P]
    [HasSheafify (lisseEtaleTopology Y) (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P]
    [∀ P : (lisseEtaleSite Y)ᵒᵖ ⥤ Type u, (lisseEtaleInclusion Y).op.HasPointwiseRightKanExtension P]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleMap f ⋙ lisseEtaleInclusion Y).op.HasPointwiseRightKanExtension P]
    [(lisseEtaleTopology X).HasSheafCompose (forget RingCat.{u})]
    [X.etaleTopology.HasSheafCompose (forget RingCat.{u})]
    [(lisseEtaleTopology Y).HasSheafCompose (forget RingCat.{u})]
    [Y.etaleTopology.HasSheafCompose (forget RingCat.{u})],
    (lisseEtaleFunctorialSquare f).cell.homIso =
      lisseEtaleFunctorialSquare_homIso f)

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleLowerShriekInverseImageIso :
  ∀ (f : X ⟶ Y) [Smooth f]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [HasSheafify X.etaleTopology (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleMap f).op.HasPointwiseRightKanExtension P]
    [HasSheafify Y.etaleTopology (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleInclusion X).op.HasLeftKanExtension P]
    [∀ P : (lisseEtaleSite Y)ᵒᵖ ⥤ Type u, (lisseEtaleInclusion Y).op.HasLeftKanExtension P],
    (lisseEtaleMap f).sheafPullbackCocontinuous (Type u)
        (lisseEtaleTopology X) (lisseEtaleTopology Y) ⋙
      lisseEtaleLowerShriek X ≅
      lisseEtaleLowerShriek Y ⋙
        (toFunctor f).sheafPullbackCocontinuous (Type u)
          X.etaleTopology Y.etaleTopology)

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleLowerShriekInverseImageIso_eq :
  ∀ (f : X ⟶ Y) [Smooth f]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [HasSheafify X.etaleTopology (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleMap f).op.HasPointwiseRightKanExtension P]
    [HasSheafify Y.etaleTopology (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleInclusion X).op.HasLeftKanExtension P]
    [∀ P : (lisseEtaleSite Y)ᵒᵖ ⥤ Type u, (lisseEtaleInclusion Y).op.HasLeftKanExtension P],
    lisseEtaleLowerShriekInverseImageIso f =
      Adjunction.leftAdjointUniq
        ((((lisseEtaleMap f).sheafPullbackCocontinuousAdjunction
                (lisseEtaleTopology X) (lisseEtaleTopology Y)).comp
            (lisseEtaleLowerShriek.adjunction X)).ofNatIsoRight
          (lisseEtalePushforwardRestrictionIso f))
        ((lisseEtaleLowerShriek.adjunction Y).comp
          ((toFunctor f).sheafPullbackCocontinuousAdjunction
            X.etaleTopology Y.etaleTopology)))

#check (AlgebraicGeometry.AlgebraicStack.flatFppfBeckChevalleySquare :
  ∀ (f : X ⟶ Y) [Flat f],
    CatCommSq (flatFppfInclusion X) (flatFppfMap f) (toFunctor f)
      (flatFppfInclusion Y))

#check (AlgebraicGeometry.AlgebraicStack.flatFppfBeckChevalleySquare_iso :
  ∀ (f : X ⟶ Y) [Flat f],
    (flatFppfBeckChevalleySquare f).iso = (flatFppfMap_comp_ι f).symm)

#check (AlgebraicGeometry.AlgebraicStack.flatFppfPushforwardRestrictionComparison :
  ∀ (f : X ⟶ Y) [Flat f]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [HasSheafify (inheritedFppfTopology X) (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfMap f).op.HasPointwiseRightKanExtension P],
    (toFunctor f).sheafPushforwardCocontinuous (Type u)
        (inheritedFppfTopology X) (inheritedFppfTopology Y) ⋙
      (flatFppfInclusion Y).sheafPushforwardContinuous (Type u)
        (flatFppfTopology Y) (inheritedFppfTopology Y) ⟶
      (flatFppfInclusion X).sheafPushforwardContinuous (Type u)
        (flatFppfTopology X) (inheritedFppfTopology X) ⋙
        (flatFppfMap f).sheafPushforwardCocontinuous (Type u)
          (flatFppfTopology X) (flatFppfTopology Y))

#check (AlgebraicGeometry.AlgebraicStack.flatFppfPushforwardRestrictionComparison_eq :
  ∀ (f : X ⟶ Y) [Flat f]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [HasSheafify (inheritedFppfTopology X) (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfMap f).op.HasPointwiseRightKanExtension P],
    flatFppfPushforwardRestrictionComparison f =
      CatCommSq.BeckChevalley.comparison.{u} (flatFppfTopology X)
        (inheritedFppfTopology X) (flatFppfTopology Y)
        (inheritedFppfTopology Y) (flatFppfBeckChevalleySquare f))

#check (AlgebraicGeometry.AlgebraicStack.flatFppfPushforwardRestrictionComparison.instIsIso :
  ∀ (f : X ⟶ Y) [Flat f]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [HasSheafify (inheritedFppfTopology X) (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfMap f).op.HasPointwiseRightKanExtension P],
    IsIso (flatFppfPushforwardRestrictionComparison f))

#check (AlgebraicGeometry.AlgebraicStack.flatFppfPushforwardRestrictionIso :
  ∀ (f : X ⟶ Y) [Flat f]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [HasSheafify (inheritedFppfTopology X) (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfMap f).op.HasPointwiseRightKanExtension P],
    (flatFppfInclusion X).sheafPushforwardContinuous (Type u)
        (flatFppfTopology X) (inheritedFppfTopology X) ⋙
      (flatFppfMap f).sheafPushforwardCocontinuous (Type u)
        (flatFppfTopology X) (flatFppfTopology Y) ≅
      (toFunctor f).sheafPushforwardCocontinuous (Type u)
        (inheritedFppfTopology X) (inheritedFppfTopology Y) ⋙
        (flatFppfInclusion Y).sheafPushforwardContinuous (Type u)
          (flatFppfTopology Y) (inheritedFppfTopology Y))

#check (AlgebraicGeometry.AlgebraicStack.flatFppfPushforwardRestrictionIso_eq :
  ∀ (f : X ⟶ Y) [Flat f]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [HasSheafify (inheritedFppfTopology X) (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfMap f).op.HasPointwiseRightKanExtension P],
    flatFppfPushforwardRestrictionIso f =
      (asIso (flatFppfPushforwardRestrictionComparison f)).symm)

#check (AlgebraicGeometry.AlgebraicStack.flatFppfFunctorialSquare_homIso :
  ∀ (f : X ⟶ Y) [Flat f]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [HasSheafify (inheritedFppfTopology X) (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfMap f).op.HasPointwiseRightKanExtension P]
    [HasSheafify (flatFppfTopology Y) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfInclusion X).op.HasPointwiseRightKanExtension P]
    [∀ P : (flatFppfSite Y)ᵒᵖ ⥤ Type u, (flatFppfInclusion Y).op.HasPointwiseRightKanExtension P]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfMap f ⋙ flatFppfInclusion Y).op.HasPointwiseRightKanExtension P]
    [(flatFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(flatFppfTopology Y).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology Y).HasSheafCompose (forget RingCat.{u})],
    (comp (flatFppfRingedToposHom X) (inheritedFppfRingedToposHom f)).toTopos.pushforward ≅
      (comp (flatFppfMap.ringedToposHom f) (flatFppfRingedToposHom Y)).toTopos.pushforward)

#check (AlgebraicGeometry.AlgebraicStack.flatFppfFunctorialSquare_homIso_eq :
  ∀ (f : X ⟶ Y) [Flat f]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [HasSheafify (inheritedFppfTopology X) (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfMap f).op.HasPointwiseRightKanExtension P]
    [HasSheafify (flatFppfTopology Y) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfInclusion X).op.HasPointwiseRightKanExtension P]
    [∀ P : (flatFppfSite Y)ᵒᵖ ⥤ Type u, (flatFppfInclusion Y).op.HasPointwiseRightKanExtension P]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfMap f ⋙ flatFppfInclusion Y).op.HasPointwiseRightKanExtension P]
    [(flatFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(flatFppfTopology Y).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology Y).HasSheafCompose (forget RingCat.{u})],
    flatFppfFunctorialSquare_homIso f =
      sheafPushforwardCocontinuousComp' (flatFppfTopology X)
          (inheritedFppfTopology X) (inheritedFppfTopology Y)
          (flatFppfInclusion X) (toFunctor f) (flatFppfMap_comp_ι f).symm ≪≫
        (sheafPushforwardCocontinuousComp (flatFppfTopology X)
          (flatFppfTopology Y) (inheritedFppfTopology Y) (flatFppfMap f)
          (flatFppfInclusion Y)).symm)

#check (AlgebraicGeometry.AlgebraicStack.flatFppfFunctorialSquare_homIso_comm :
  ∀ (f : X ⟶ Y) [Flat f]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [HasSheafify (inheritedFppfTopology X) (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfMap f).op.HasPointwiseRightKanExtension P]
    [HasSheafify (flatFppfTopology Y) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfInclusion X).op.HasPointwiseRightKanExtension P]
    [∀ P : (flatFppfSite Y)ᵒᵖ ⥤ Type u, (flatFppfInclusion Y).op.HasPointwiseRightKanExtension P]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfMap f ⋙ flatFppfInclusion Y).op.HasPointwiseRightKanExtension P]
    [(flatFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(flatFppfTopology Y).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology Y).HasSheafCompose (forget RingCat.{u})],
    (comp (flatFppfRingedToposHom X)
          (inheritedFppfRingedToposHom f)).directStructureMap ≫
        (MorphismOfTopoiIn.ringDirectImageNatTrans
          (flatFppfFunctorialSquare_homIso f).hom).app
          (flatFppfRingedSite X).structureSheaf =
      (comp (flatFppfMap.ringedToposHom f)
        (flatFppfRingedToposHom Y)).directStructureMap)

#check (AlgebraicGeometry.AlgebraicStack.flatFppfFunctorialSquare :
  ∀ (f : X ⟶ Y) [Flat f]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [HasSheafify (inheritedFppfTopology X) (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfMap f).op.HasPointwiseRightKanExtension P]
    [HasSheafify (flatFppfTopology Y) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfInclusion X).op.HasPointwiseRightKanExtension P]
    [∀ P : (flatFppfSite Y)ᵒᵖ ⥤ Type u, (flatFppfInclusion Y).op.HasPointwiseRightKanExtension P]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfMap f ⋙ flatFppfInclusion Y).op.HasPointwiseRightKanExtension P]
    [(flatFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(flatFppfTopology Y).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology Y).HasSheafCompose (forget RingCat.{u})],
    CommSquare (flatFppfRingedSite X) (ringedSite X)
      (flatFppfRingedSite Y) (ringedSite Y))

#check (AlgebraicGeometry.AlgebraicStack.flatFppfFunctorialSquare_upper :
  ∀ (f : X ⟶ Y) [Flat f]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [HasSheafify (inheritedFppfTopology X) (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfMap f).op.HasPointwiseRightKanExtension P]
    [HasSheafify (flatFppfTopology Y) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfInclusion X).op.HasPointwiseRightKanExtension P]
    [∀ P : (flatFppfSite Y)ᵒᵖ ⥤ Type u, (flatFppfInclusion Y).op.HasPointwiseRightKanExtension P]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfMap f ⋙ flatFppfInclusion Y).op.HasPointwiseRightKanExtension P]
    [(flatFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(flatFppfTopology Y).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology Y).HasSheafCompose (forget RingCat.{u})],
    (flatFppfFunctorialSquare f).upper = flatFppfRingedToposHom X)

#check (AlgebraicGeometry.AlgebraicStack.flatFppfFunctorialSquare_left :
  ∀ (f : X ⟶ Y) [Flat f]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [HasSheafify (inheritedFppfTopology X) (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfMap f).op.HasPointwiseRightKanExtension P]
    [HasSheafify (flatFppfTopology Y) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfInclusion X).op.HasPointwiseRightKanExtension P]
    [∀ P : (flatFppfSite Y)ᵒᵖ ⥤ Type u, (flatFppfInclusion Y).op.HasPointwiseRightKanExtension P]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfMap f ⋙ flatFppfInclusion Y).op.HasPointwiseRightKanExtension P]
    [(flatFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(flatFppfTopology Y).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology Y).HasSheafCompose (forget RingCat.{u})],
    (flatFppfFunctorialSquare f).left = flatFppfMap.ringedToposHom f)

#check (AlgebraicGeometry.AlgebraicStack.flatFppfFunctorialSquare_right :
  ∀ (f : X ⟶ Y) [Flat f]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [HasSheafify (inheritedFppfTopology X) (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfMap f).op.HasPointwiseRightKanExtension P]
    [HasSheafify (flatFppfTopology Y) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfInclusion X).op.HasPointwiseRightKanExtension P]
    [∀ P : (flatFppfSite Y)ᵒᵖ ⥤ Type u, (flatFppfInclusion Y).op.HasPointwiseRightKanExtension P]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfMap f ⋙ flatFppfInclusion Y).op.HasPointwiseRightKanExtension P]
    [(flatFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(flatFppfTopology Y).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology Y).HasSheafCompose (forget RingCat.{u})],
    (flatFppfFunctorialSquare f).right = inheritedFppfRingedToposHom f)

#check (AlgebraicGeometry.AlgebraicStack.flatFppfFunctorialSquare_lower :
  ∀ (f : X ⟶ Y) [Flat f]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [HasSheafify (inheritedFppfTopology X) (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfMap f).op.HasPointwiseRightKanExtension P]
    [HasSheafify (flatFppfTopology Y) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfInclusion X).op.HasPointwiseRightKanExtension P]
    [∀ P : (flatFppfSite Y)ᵒᵖ ⥤ Type u, (flatFppfInclusion Y).op.HasPointwiseRightKanExtension P]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfMap f ⋙ flatFppfInclusion Y).op.HasPointwiseRightKanExtension P]
    [(flatFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(flatFppfTopology Y).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology Y).HasSheafCompose (forget RingCat.{u})],
    (flatFppfFunctorialSquare f).lower = flatFppfRingedToposHom Y)

#check (AlgebraicGeometry.AlgebraicStack.flatFppfFunctorialSquare_homIso_eq_cell :
  ∀ (f : X ⟶ Y) [Flat f]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [HasSheafify (inheritedFppfTopology X) (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfMap f).op.HasPointwiseRightKanExtension P]
    [HasSheafify (flatFppfTopology Y) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfInclusion X).op.HasPointwiseRightKanExtension P]
    [∀ P : (flatFppfSite Y)ᵒᵖ ⥤ Type u, (flatFppfInclusion Y).op.HasPointwiseRightKanExtension P]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfMap f ⋙ flatFppfInclusion Y).op.HasPointwiseRightKanExtension P]
    [(flatFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(flatFppfTopology Y).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology Y).HasSheafCompose (forget RingCat.{u})],
    (flatFppfFunctorialSquare f).cell.homIso =
      flatFppfFunctorialSquare_homIso f)

#check (AlgebraicGeometry.AlgebraicStack.flatFppfLowerShriekInverseImageIso :
  ∀ (f : X ⟶ Y) [Flat f]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [HasSheafify (inheritedFppfTopology X) (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfMap f).op.HasPointwiseRightKanExtension P]
    [HasSheafify (inheritedFppfTopology Y) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfInclusion X).op.HasLeftKanExtension P]
    [∀ P : (flatFppfSite Y)ᵒᵖ ⥤ Type u, (flatFppfInclusion Y).op.HasLeftKanExtension P],
    (flatFppfMap f).sheafPullbackCocontinuous (Type u)
        (flatFppfTopology X) (flatFppfTopology Y) ⋙
      flatFppfLowerShriek X ≅
      flatFppfLowerShriek Y ⋙
        (toFunctor f).sheafPullbackCocontinuous (Type u)
          (inheritedFppfTopology X) (inheritedFppfTopology Y))

#check (AlgebraicGeometry.AlgebraicStack.flatFppfLowerShriekInverseImageIso_eq :
  ∀ (f : X ⟶ Y) [Flat f]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [HasSheafify (inheritedFppfTopology X) (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfMap f).op.HasPointwiseRightKanExtension P]
    [HasSheafify (inheritedFppfTopology Y) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfInclusion X).op.HasLeftKanExtension P]
    [∀ P : (flatFppfSite Y)ᵒᵖ ⥤ Type u, (flatFppfInclusion Y).op.HasLeftKanExtension P],
    flatFppfLowerShriekInverseImageIso f =
      Adjunction.leftAdjointUniq
        ((((flatFppfMap f).sheafPullbackCocontinuousAdjunction
                (flatFppfTopology X) (flatFppfTopology Y)).comp
            (flatFppfLowerShriek.adjunction X)).ofNatIsoRight
          (flatFppfPushforwardRestrictionIso f))
        ((flatFppfLowerShriek.adjunction Y).comp
          ((toFunctor f).sheafPullbackCocontinuousAdjunction
            (inheritedFppfTopology X) (inheritedFppfTopology Y))))

end AlgebraicGeometry.AlgebraicStack
