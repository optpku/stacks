module

import StacksCheckRecall
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap96.Lemma_96_10_1_Comparison
public import stacks_project.Chap96.«96_10_2_1_Restriction»

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
variable [(AlgebraicSpace.smallEtaleTopology F).HasSheafCompose (forget RingCat.{u})]
variable [X.etaleTopology.HasSheafCompose (forget RingCat.{u})]
variable [(forget RingCat.{u}).PreservesRightKanExtensions (smallEtaleFunctor F X j).op]
variable [HasWeakSheafify X.etaleTopology (Type u)]
variable [∀ P : (AlgebraicSpace.smallEtaleSite F)ᵒᵖ ⥤ Type u,
    (smallEtaleFunctor F X j).op.HasLeftKanExtension P]
variable [PreservesFiniteLimits
    ((smallEtaleFunctor F X j).sheafPullback (Type u)
      (AlgebraicSpace.smallEtaleTopology F) X.etaleTopology)]

/- 96.10.2.1 If an algebraic stack X over S is represented by an algebraic space F,
with equivalence j : F.toGroupoids ≌ X inducing the continuous cocontinuous functor
u = smallEtaleFunctor F X j : smallEtaleSite F ⥤ X.total, then restriction of an
étale sheaf ℱ is ℱ|_{F_étale} = i_F⁻¹ ℱ = π_{F,*} ℱ. -/
@[stacks 075K]
#check (AlgebraicSpace.restrictSheaf F X j = (inclusionToTopos F X j)⁻¹ ∧
    AlgebraicSpace.restrictSheaf F X j = (piToTopos F X j).pushforward)
