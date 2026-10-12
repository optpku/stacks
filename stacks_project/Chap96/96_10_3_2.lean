/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import stacks_project.Chap96.«96_10_3_2_Comparison»

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open FiberedCategoryOver.Groupoids AlgebraicGeometry.GroupoidsOver
open scoped Bicategory

universe u

variable {S : Scheme.{u}} {X : GroupoidsOver S}
variable {U V : AlgebraicSpace S} (a : U ⟶ V)
variable (f : U.toGroupoids ⟶ X) (g : V.toGroupoids ⟶ X)
variable (φ : toGroupoids.map a ≫ g ≅ f)
variable (F : Sheaf X.etaleTopology (Type (u + 1)))
variable [HasSheafify U.toGroupoids.etaleTopology (Type (u + 1))]
variable [HasSheafify V.toGroupoids.etaleTopology (Type (u + 1))]
variable [HasWeakSheafify X.etaleTopology (Type (u + 1))]
variable [HasWeakSheafify V.toGroupoids.etaleTopology (Type (u + 1))]
variable [∀ P : U.toGroupoids.totalᵒᵖ ⥤ Type (u + 1),
    (toCartesianBasedFunctor f).toFunctor.op.HasPointwiseRightKanExtension P]
variable [∀ P : V.toGroupoids.totalᵒᵖ ⥤ Type (u + 1),
    (toCartesianBasedFunctor g).toFunctor.op.HasPointwiseRightKanExtension P]
variable [∀ P : U.toGroupoids.totalᵒᵖ ⥤ Type (u + 1),
    (toCartesianBasedFunctor (toGroupoids.map a)).toFunctor.op.HasPointwiseRightKanExtension P]
variable [∀ P : U.toGroupoids.totalᵒᵖ ⥤ Type (u + 1),
    (toCartesianBasedFunctor (toGroupoids.map a ≫ g)).toFunctor.op.HasPointwiseRightKanExtension P]

/- 96.10.3.2 For a 2-commutative triangle of 1-morphisms of categories fibred in
groupoids over (Sch/S)_fppf with U, V represented by algebraic spaces and F an
étale sheaf on X, the comparison morphism algebraicSpaceComparison φ F is the
adjunct a_small⁻¹(g⁻¹ F|_{V_étale}) ⟶ f⁻¹ F|_{U_étale} of comparisonPushforward,
obtained via (Adjunction.ofIsRightAdjoint (sheafPushforwardType a)).homEquiv.symm. -/
@[stacks 076Q]
#check (algebraicSpaceComparison a f g φ F :
    (sheafPushforwardType a).leftAdjoint.obj
        ((restrictEtale V).obj ((etaleInverseImage g).obj F)) ⟶
      (restrictEtale U).obj ((etaleInverseImage f).obj F))
