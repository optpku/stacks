module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Category
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.CostructuredArrow.Bilimit
public import stacks_project.Chap99.Remark_99_15_5_BaseChange
import StacksCheckRecall

/-!
# Remark 99.15.5

The pair category `B-Curves` sits in a 2-fibre product square over the absolute
category of curves along schemes over `B`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.Spaces
open CategoricalPullback

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces

variable {S : Scheme.{u}} (B : AlgebraicSpace S)

/- Remark 99.15.5: the category `CurvesGroupoidsOver B` of pairs
`(X ⟶ S in Curves.Obj, h : S ⟶ B)` sits in a 2-fibre product square over
`Curves.p : Curves.Obj S ⥤ Over S` along `SchemeOver B ⥤ Over S`. -/
@[stacks 0D54] #check
  (CategoryTheory.Limits.CategoricalPullback.CostructuredArrow.instSquareIsBilimit
    (Curves.p S) (ofOverFunctor S) B :
    CatCommSqOver.Resized.IsBilimit (CurvesGroupoidsOver.square B))

end AlgebraicGeometry.AlgebraicSpace.Spaces
