module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Smooth.Comparison
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 34.5.2: Any étale covering is a smooth covering, and a fortiori, any Zariski
covering is a smooth covering. -/
@[stacks 0220] #check
  (AlgebraicGeometry.Scheme.etalePrecoverage_le_bigSmoothPrecoverage :
    AlgebraicGeometry.Scheme.etalePrecoverage.{u} ≤
      AlgebraicGeometry.Scheme.bigSmoothPrecoverage.{u})

#check
  (AlgebraicGeometry.Scheme.zariskiPrecoverage_le_bigSmoothPrecoverage :
    AlgebraicGeometry.Scheme.zariskiPrecoverage.{u} ≤
      AlgebraicGeometry.Scheme.bigSmoothPrecoverage.{u})
