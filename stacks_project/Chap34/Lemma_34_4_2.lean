module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Zariski
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 34.4.2: Any Zariski covering is an étale covering. -/
@[stacks 0216] #check
  (AlgebraicGeometry.Scheme.zariskiPrecoverage_le_etalePrecoverage :
    AlgebraicGeometry.Scheme.zariskiPrecoverage.{u} ≤
      AlgebraicGeometry.Scheme.etalePrecoverage.{u})
