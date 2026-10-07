module

public import stacks_project.Chap99.Remark_99_13_5_BaseChange

/-!
# Remark 99.13.5

The pair categories `B-Spaces'_ft` and `B-Spaces'_{fp, flat, proper}` sit in 2-fibre
product squares over the absolute primed categories along schemes over `B`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.Spaces
open CategoricalPullback

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces

/-- Remark 99.13.5 (1): the category `FtGroupoidsOver B` of pairs
`(X ⟶ S in FtGroupoids, h : S ⟶ B)` sits in a 2-fibre product square over
`pFtGroupoids : FtGroupoids S ⥤ Over S` along `SchemeOver B ⥤ Over S`. -/
@[stacks 0D1H, instance]
instance FtGroupoidsOver.instSquareIsBilimit {S : Scheme.{u}} (B : AlgebraicSpace S) :
    CatCommSqOver.Resized.IsBilimit (FtGroupoidsOver.square B) :=
  sorry

/-- Remark 99.13.5 (2): a similar construction yields a 2-fibre product square for
`FpFlatProperGroupoidsOver B`, the category `B-Spaces'_{fp, flat, proper}`. -/
@[stacks 0D1H, instance]
instance FpFlatProperGroupoidsOver.instSquareIsBilimit {S : Scheme.{u}}
    (B : AlgebraicSpace S) :
    CatCommSqOver.Resized.IsBilimit (FpFlatProperGroupoidsOver.square B) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Spaces
