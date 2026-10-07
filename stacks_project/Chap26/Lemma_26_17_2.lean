module

import StacksCheckRecall
public import Mathlib.AlgebraicGeometry.Pullbacks

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

universe u

variable {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
variable [IsAffine X] [IsAffine Y] [IsAffine S]

/- Lemma 26.17.2: a fibre product of affine schemes over an affine scheme
is affine. -/
@[stacks 01JQ]
#check Scheme.Pullback.isAffine_of_isAffine_isAffine_isAffine f g
