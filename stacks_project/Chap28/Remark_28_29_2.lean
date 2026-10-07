module

public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.AffineOpenCounterexample
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

/- Remark 28.29.2: Let `R = ℚ[x, y₁, y₂, …] / ((x - i)yᵢ)` and let
`p = (y₁, y₂, …)` be its minimal prime ideal. Gluing two copies of `Spec R` along
`Spec R \ V(p)` gives a non-quasi-separated scheme. The two points corresponding
to `p` are distinct generic points and do not lie in a common affine open. -/
@[stacks 01ZW] #check
  (AlgebraicGeometry.RationalLineArrangement.DoubleAlong.counterexample :
    ¬ QuasiSeparatedSpace AlgebraicGeometry.RationalLineArrangement.DoubleAlong.scheme ∧
      ¬ ∃ U : AlgebraicGeometry.RationalLineArrangement.DoubleAlong.scheme.affineOpens,
        ∀ i,
          (AlgebraicGeometry.RationalLineArrangement.DoubleAlong.genericPointsEmbedding i :
              AlgebraicGeometry.RationalLineArrangement.DoubleAlong.scheme) ∈
            ((U : AlgebraicGeometry.RationalLineArrangement.DoubleAlong.scheme.Opens) :
              Set AlgebraicGeometry.RationalLineArrangement.DoubleAlong.scheme))
