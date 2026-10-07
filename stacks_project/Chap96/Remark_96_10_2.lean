module

import StacksCheckRecall
public import stacks_project.Chap96.Remark_96_10_2_Comparison

/-!
# Remark 96.10.2

If `f : X ⟶ Y` is a 1-morphism of categories fibred in groupoids over
`(Sch/S)_fppf`, `X` and `Y` are represented by algebraic spaces `F` and `G`,
and the induced morphism `F ⟶ G` is étale, then the two stacked squares of
ringed topoi with horizontal edges `f_small`, `f`, `f_small` and vertical edges
`i_F`, `π_F` on the left and `i_G`, `π_G` on the right commute.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory AlgebraicGeometry.GroupoidsOver
open CategoryTheory.Functor FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

variable {S : Scheme.{u}}
variable {X Y : GroupoidsOver S} (f : X ⟶ Y)
variable {F G : AlgebraicSpace S} (eX : F.toGroupoids ≌ X) (eY : G.toGroupoids ≌ Y)
variable (α : (f ≫ eY.symm.hom) ≅
    (eX.symm.hom ≫ AlgebraicSpace.toGroupoids.map (inducedHom eX eY f)))
variable [AlgebraicSpace.Etale (inducedHom eX eY f)]
variable [HasSheafify (AlgebraicSpace.smallEtaleTopology F) (Type u)]
variable [HasSheafify (AlgebraicSpace.smallEtaleTopology G) (Type u)]
variable [∀ P : (AlgebraicSpace.smallEtaleSite F)ᵒᵖ ⥤ Type u,
    (smallEtaleFunctor F X eX).op.HasPointwiseRightKanExtension P]
variable [∀ P : (AlgebraicSpace.smallEtaleSite G)ᵒᵖ ⥤ Type u,
    (smallEtaleFunctor G Y eY).op.HasPointwiseRightKanExtension P]
variable [∀ P : (AlgebraicSpace.smallEtaleSite F)ᵒᵖ ⥤ RingCat.{u},
    (smallEtaleFunctor F X eX).op.HasPointwiseRightKanExtension P]
variable [∀ P : (AlgebraicSpace.smallEtaleSite G)ᵒᵖ ⥤ RingCat.{u},
    (smallEtaleFunctor G Y eY).op.HasPointwiseRightKanExtension P]
variable [(forget RingCat.{u}).PreservesRightKanExtensions (smallEtaleFunctor F X eX).op]
variable [(forget RingCat.{u}).PreservesRightKanExtensions (smallEtaleFunctor G Y eY).op]
variable [∀ P : (AlgebraicSpace.smallEtaleSite F)ᵒᵖ ⥤ Type u,
    (smallEtaleFunctor F X eX).op.HasLeftKanExtension P]
variable [∀ P : (AlgebraicSpace.smallEtaleSite G)ᵒᵖ ⥤ Type u,
    (smallEtaleFunctor G Y eY).op.HasLeftKanExtension P]
variable [∀ P : X.totalᵒᵖ ⥤ Type u,
    (toCartesianBasedFunctor f).toFunctor.op.HasPointwiseRightKanExtension P]
variable [∀ P : F.toGroupoids.totalᵒᵖ ⥤ Type u,
    (toCartesianBasedFunctor
        (AlgebraicSpace.toGroupoids.map (inducedHom eX eY f))).toFunctor.op.HasPointwiseRightKanExtension P]
variable [∀ P : (AlgebraicSpace.smallEtaleSite F)ᵒᵖ ⥤ Type u,
    (AlgebraicSpace.smallEtaleInclusion F).op.HasPointwiseRightKanExtension P]
variable [∀ P : (AlgebraicSpace.smallEtaleSite F)ᵒᵖ ⥤ Type u,
    (AlgebraicSpace.etaleRestriction (inducedHom eX eY f)).op.HasPointwiseRightKanExtension P]
variable [∀ P : (AlgebraicSpace.smallEtaleSite F)ᵒᵖ ⥤ Type u,
    (smallEtaleFunctor F X eX ⋙ (toCartesianBasedFunctor f).toFunctor).op.HasPointwiseRightKanExtension P]
variable [∀ P : (AlgebraicSpace.smallEtaleSite F)ᵒᵖ ⥤ Type u,
    (AlgebraicSpace.etaleRestriction (inducedHom eX eY f) ⋙
        smallEtaleFunctor G Y eY).op.HasPointwiseRightKanExtension P]

/- Remark 96.10.2 (1): the square of ringed topoi with edges `f_small`, `i_F`, `i_G`,
and `f` is commutative when the induced morphism `F ⟶ G` is étale. -/
@[stacks 0GQA]
#check (compareInclusion eX eY f α :
    RingedSite.ToposHom.CommSquare (AlgebraicSpace.ringedSite F)
      (AlgebraicSpace.ringedSite G) (etaleRingedSite X) (etaleRingedSite Y))

/- Remark 96.10.2 (2): the square of ringed topoi with edges `f`, `π_F`, `π_G`, and
`f_small` is commutative. -/
@[stacks 0GQA]
#check (compareMorphism eX eY f α :
    RingedSite.ToposHom.CommSquare (etaleRingedSite X) (etaleRingedSite Y)
      (AlgebraicSpace.ringedSite F) (AlgebraicSpace.ringedSite G))
