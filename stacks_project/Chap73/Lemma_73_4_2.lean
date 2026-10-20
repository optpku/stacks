module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtalePrecoverage.Zariski
import StacksCheckRecall

/-!
# Zariski coverings are étale coverings

Every Zariski covering family of algebraic spaces over a scheme S is an
étale covering family.
-/

@[expose] public section

open AlgebraicGeometry

universe u

/- Lemma 73.4.2: any Zariski covering is an étale covering. -/
@[stacks 0DF1] #check
  (AlgebraicGeometry.AlgebraicSpace.zariskiPrecoverage_le_etalePrecoverage :
    ∀ {S : Scheme.{u}},
      AlgebraicGeometry.AlgebraicSpace.zariskiPrecoverage S ≤
        AlgebraicGeometry.AlgebraicSpace.etalePrecoverage)
