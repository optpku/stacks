/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.SpaceInverseImageComparison

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open FiberedCategoryOver.Groupoids AlgebraicGeometry.GroupoidsOver
open scoped Bicategory

universe u

/- 96.10.3.2 For a 2-commutative triangle of categories fibred in groupoids
with algebraic-space legs, the small étale inverse-image comparison is the
adjunct of the restricted unit under sheafAdjunctionType. -/
@[stacks 076Q] #check (AlgebraicGeometry.GroupoidsOver.algebraicSpaceComparison :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} {U V : AlgebraicSpace S}
      (a : U ⟶ V) (f : U.toGroupoids ⟶ X) (g : V.toGroupoids ⟶ X)
      (φ : toGroupoids.map a ≫ g ≅ f)
      [HasSheafify U.toGroupoids.etaleTopology (Type (u + 1))]
      [HasSheafify V.toGroupoids.etaleTopology (Type (u + 1))]
      [HasWeakSheafify X.etaleTopology (Type (u + 1))]
      [HasWeakSheafify V.toGroupoids.etaleTopology (Type (u + 1))]
      [∀ P : U.toGroupoids.totalᵒᵖ ⥤ Type (u + 1),
        (toCartesianBasedFunctor f).toFunctor.op.HasPointwiseRightKanExtension P]
      [∀ P : V.toGroupoids.totalᵒᵖ ⥤ Type (u + 1),
        (toCartesianBasedFunctor g).toFunctor.op.HasPointwiseRightKanExtension P]
      [∀ P : U.toGroupoids.totalᵒᵖ ⥤ Type (u + 1),
        (toCartesianBasedFunctor (toGroupoids.map a)).toFunctor.op.HasPointwiseRightKanExtension P]
      [∀ P : U.toGroupoids.totalᵒᵖ ⥤ Type (u + 1),
        (toCartesianBasedFunctor (toGroupoids.map a ≫ g)).toFunctor.op.HasPointwiseRightKanExtension P]
      (F : Sheaf X.etaleTopology (Type (u + 1))),
      (AlgebraicGeometry.AlgebraicSpace.sheafTypeInverseImage a).obj
          ((AlgebraicGeometry.AlgebraicSpace.restrictEtale V).obj
            ((AlgebraicGeometry.GroupoidsOver.etaleInverseImage g).obj F)) ⟶
        (AlgebraicGeometry.AlgebraicSpace.restrictEtale U).obj
          ((AlgebraicGeometry.GroupoidsOver.etaleInverseImage f).obj F))
