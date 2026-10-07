module

import ReasLib.AlgebraicGeometry.Scheme.Cover.Fpqc.DoubledOriginCounterexample
import StacksCheckRecall

universe u

/- Example 34.9.3: for countably infinite affine space over a field, the singleton coproduct
family formed from the first chart of the doubled-origin scheme and the spectrum of the local
ring at the origin of the second chart satisfies the pointwise finite quasi-compact neighborhood
criterion, but it is not an fpqc covering. -/
@[stacks 0H7E]
#check
  (AlgebraicGeometry.PuncturedAffineSpace.DoubleAlong.FpqcCounterexample.neighborhood_and_not_fpqcCovering :
    ∀ (k : Type u) [Field k],
      AlgebraicGeometry.Scheme.Fpqc.Criterion.Neighborhood
          (AlgebraicGeometry.PuncturedAffineSpace.DoubleAlong.FpqcCounterexample.singletonFamily k) ∧
        ¬ AlgebraicGeometry.Scheme.FpqcCovering
          (AlgebraicGeometry.PuncturedAffineSpace.DoubleAlong.FpqcCounterexample.singletonFamily k))
