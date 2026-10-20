module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Spaces.BaseChange
import StacksCheckRecall

/-!
# Remark 99.13.5

The pair categories B-Spaces'_ft and B-Spaces'_{fp, flat, proper} sit in
2-fibre product squares over the corresponding primed family categories.
The relative formulation below specializes at S = Spec ℤ to the stated
absolute case: schemes have their canonical morphism to Spec ℤ.
The fppf site notation specifies the topology and imposes no extra restriction
on the underlying morphisms in these categories.
-/

universe u

/- Remark 99.13.5: finite-type primed families with a morphism from their base
scheme to B form the prescribed 2-fibre product. -/
@[stacks 0D1H] #check
  (AlgebraicGeometry.AlgebraicSpace.Spaces.FtGroupoidsOver.instSquareIsBilimit :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (B : AlgebraicGeometry.AlgebraicSpace S),
      CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.Resized.IsBilimit
        (AlgebraicGeometry.AlgebraicSpace.Spaces.FtGroupoidsOver.square B))

/- Remark 99.13.5: the same construction applies to finite-presentation,
flat, proper primed families. -/
@[stacks 0D1H] #check
  (AlgebraicGeometry.AlgebraicSpace.Spaces.FpFlatProperGroupoidsOver.instSquareIsBilimit :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (B : AlgebraicGeometry.AlgebraicSpace S),
      CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.Resized.IsBilimit
        (AlgebraicGeometry.AlgebraicSpace.Spaces.FpFlatProperGroupoidsOver.square B))
