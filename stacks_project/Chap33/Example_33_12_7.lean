module

public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Regular.RationalFunctionCounterexample
import StacksCheckRecall

@[expose] public section

/- The hypersurface `x ^ p = t` is a variety over `𝔽_p(t)`. -/
#check
  (AlgebraicGeometry.RationalFunctionRegularityCounterexample.InseparablePoint.overBase_variety :
    ∀ (p : ℕ) [Fact p.Prime],
      AlgebraicGeometry.Variety
        (AlgebraicGeometry.RationalFunctionRegularityCounterexample.InseparablePoint.overBase p))

/- The hypersurface `x ^ p = t` is regular. -/
#check
  (AlgebraicGeometry.RationalFunctionRegularityCounterexample.InseparablePoint.scheme_regular :
    ∀ (p : ℕ) [Fact p.Prime],
      AlgebraicGeometry.Scheme.Regular
        (AlgebraicGeometry.RationalFunctionRegularityCounterexample.InseparablePoint.scheme p))

/- The hypersurface `x ^ p = t` is not geometrically reduced over `𝔽_p(t)`. -/
#check
  (AlgebraicGeometry.RationalFunctionRegularityCounterexample.InseparablePoint.overBase_not_geometricallyReduced :
    ∀ (p : ℕ) [Fact p.Prime],
      ¬ AlgebraicGeometry.SchemeOverField.geometricallyReduced
        (AlgebraicGeometry.RationalFunctionRegularityCounterexample.InseparablePoint.overBase p))

/- For `2 < p`, the cusp `y ^ 2 - x ^ p + t = 0` is a variety over `𝔽_p(t)`. -/
#check
  (AlgebraicGeometry.RationalFunctionRegularityCounterexample.Cusp.overBase_variety :
    ∀ (p : ℕ) [Fact p.Prime], 2 < p →
      AlgebraicGeometry.Variety
        (AlgebraicGeometry.RationalFunctionRegularityCounterexample.Cusp.overBase p))

/- For `2 < p`, the cusp `y ^ 2 - x ^ p + t = 0` is regular. -/
#check
  (AlgebraicGeometry.RationalFunctionRegularityCounterexample.Cusp.scheme_regular :
    ∀ (p : ℕ) [Fact p.Prime], 2 < p →
      AlgebraicGeometry.Scheme.Regular
        (AlgebraicGeometry.RationalFunctionRegularityCounterexample.Cusp.scheme p))

/- For `2 < p`, the cusp `y ^ 2 - x ^ p + t = 0` is geometrically reduced over
`𝔽_p(t)`. -/
#check
  (AlgebraicGeometry.RationalFunctionRegularityCounterexample.Cusp.overBase_geometricallyReduced :
    ∀ (p : ℕ) [Fact p.Prime], 2 < p →
      AlgebraicGeometry.SchemeOverField.geometricallyReduced
        (AlgebraicGeometry.RationalFunctionRegularityCounterexample.Cusp.overBase p))

/- Example 33.12.7: for every prime `p > 2`, the regular geometrically reduced
variety `y ^ 2 - x ^ p + t = 0` over `𝔽_p(t)` is not geometrically normal. -/
@[stacks 038Y] #check
  (AlgebraicGeometry.RationalFunctionRegularityCounterexample.Cusp.overBase_not_geometricallyNormal :
    ∀ (p : ℕ) [Fact p.Prime], 2 < p →
      ¬ AlgebraicGeometry.SchemeOverField.geometricallyNormal
        (AlgebraicGeometry.RationalFunctionRegularityCounterexample.Cusp.overBase p))
