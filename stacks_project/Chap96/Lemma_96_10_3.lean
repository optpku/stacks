module

import StacksCheckRecall
public import stacks_project.Chap96.Lemma_96_10_3_Comparison

/-!
# Lemma 96.10.3

If `f : X ⟶ Y` is a 1-morphism of categories fibred in groupoids over
`(Sch/S)_fppf` and `X`, `Y` are represented by algebraic spaces `F`, `G`,
then the square of ringed topoi with upper edge `f`, left edge `π_F`, right
edge `π_G`, and lower edge `f_small` is commutative. The source explicitly
denies a commutative diagram of ringed sites, because `F ⟶ G` need not be
representable by schemes.
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
variable [HasSheafify (AlgebraicSpace.smallEtaleTopology F) (Type u)]
variable [HasSheafify (AlgebraicSpace.smallEtaleTopology G) (Type u)]
variable [∀ P : (AlgebraicSpace.smallEtaleSite F)ᵒᵖ ⥤ Type u,
    (smallEtaleFunctor F X eX).op.HasLeftKanExtension P]
variable [∀ P : (AlgebraicSpace.smallEtaleSite G)ᵒᵖ ⥤ Type u,
    (smallEtaleFunctor G Y eY).op.HasLeftKanExtension P]

/- Lemma 96.10.3: the square of ringed topoi with edges `f`, `π_F`, `π_G`, and
`f_small` is commutative, via the presentation 2-iso `α`. -/
@[stacks 073N]
#check (compareMorphism eX eY f α :
    RingedSite.ToposHom.CommSquare (etaleRingedSite X) (etaleRingedSite Y)
      (AlgebraicSpace.ringedSite F) (AlgebraicSpace.ringedSite G))
