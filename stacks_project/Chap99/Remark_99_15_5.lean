/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap99.Remark_99_15_5_BaseChange

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

/-- Remark 99.15.5: the category `CurvesGroupoidsOver B` of pairs
`(X ⟶ S in CurvesGroupoids, h : S ⟶ B)` sits in a 2-fibre product square over
`pCurvesGroupoids : CurvesGroupoids S ⥤ Over S` along `SchemeOver B ⥤ Over S`. -/
@[stacks 0D54, instance]
instance CurvesGroupoidsOver.instSquareIsBilimit {S : Scheme.{u}} (B : AlgebraicSpace S) :
    CatCommSqOver.Resized.IsBilimit (CurvesGroupoidsOver.square B) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Spaces
