/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.SmallEtaleComparison
public import ReasLib.CategoryTheory.Sites.Topos.Continuous

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.GroupoidsOver
open scoped Bicategory MorphismOfTopoiIn

universe u

variable {S : Scheme.{u}} (F : AlgebraicSpace S) (X : GroupoidsOver S)
variable [AlgebraicStack X] (j : F.toGroupoids ≌ X)
variable [HasSheafify (AlgebraicSpace.smallEtaleTopology F) (Type u)]
variable [∀ P : (AlgebraicSpace.smallEtaleSite F)ᵒᵖ ⥤ Type u,
    (smallEtaleFunctor F X j).op.HasPointwiseRightKanExtension P]
variable [∀ P : (AlgebraicSpace.smallEtaleSite F)ᵒᵖ ⥤ RingCat.{u},
    (smallEtaleFunctor F X j).op.HasPointwiseRightKanExtension P]
variable [(AlgebraicSpace.smallEtaleTopology F).HasSheafCompose
    (forget RingCat.{u} : RingCat.{u} ⥤ Type u)]
variable [X.etaleTopology.HasSheafCompose (forget RingCat.{u} : RingCat.{u} ⥤ Type u)]
variable [(forget RingCat.{u} : RingCat.{u} ⥤ Type u).PreservesRightKanExtensions
    (smallEtaleFunctor F X j).op]
variable [HasWeakSheafify X.etaleTopology (Type u)]
variable [∀ P : (AlgebraicSpace.smallEtaleSite F)ᵒᵖ ⥤ Type u,
    (smallEtaleFunctor F X j).op.HasLeftKanExtension P]

/- 96.10.2.1 If an algebraic stack X over S is represented by an algebraic space F,
with equivalence j : F.toGroupoids ≌ X inducing the continuous cocontinuous functor
u = smallEtaleFunctor F X j : smallEtaleSite F ⥤ X.total, then restriction of an
étale sheaf ℱ is ℱ|_{F_étale} = i_F⁻¹ ℱ = π_{F,*} ℱ. -/
@[stacks 075K]
#check (AlgebraicGeometry.GroupoidsOver.inclusionToTopos_inverseImage F X j :
    (inclusionToTopos F X j)⁻¹ =
      (smallEtaleFunctor F X j).sheafPushforwardContinuous (Type u)
        (AlgebraicSpace.smallEtaleTopology F) X.etaleTopology)

#check (CategoryTheory.Functor.morphismOfTopoiInOfContinuous_pushforward.{u}
    (smallEtaleFunctor F X j) (AlgebraicSpace.smallEtaleTopology F) X.etaleTopology :
    (piToTopos F X j).pushforward =
      (smallEtaleFunctor F X j).sheafPushforwardContinuous (Type u)
        (AlgebraicSpace.smallEtaleTopology F) X.etaleTopology)

variable (ℱ : Sheaf X.etaleTopology (Type u)) (U : AlgebraicSpace.smallEtaleSite F)

#check (CategoryTheory.Functor.sheafPushforwardContinuousObjObjIso
    (smallEtaleFunctor F X j) (Type u) ℱ U :
    (((smallEtaleFunctor F X j).sheafPushforwardContinuous (Type u)
        (AlgebraicSpace.smallEtaleTopology F) X.etaleTopology).obj ℱ).obj.obj
        (Opposite.op U) ≅
      ℱ.obj.obj (Opposite.op ((smallEtaleFunctor F X j).obj U)))
