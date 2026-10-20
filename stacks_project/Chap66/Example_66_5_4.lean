module

public import Mathlib.Algebra.Field.ULift
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.Quotient
import StacksCheckRecall

/-!
# Quasi-compactness of 𝔸¹_ℚ / ℤ
-/

@[expose] public section

universe u

/- Example 66.5.4: the space 𝔸¹_ℚ / ℤ is a quasi-compact algebraic space. -/
@[stacks 03IO] #check
  (AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.instIsQuasiCompact (ULift.{u} ℚ) :
    AlgebraicGeometry.AlgebraicSpace.IsQuasiCompact
      (AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.space (ULift.{u} ℚ)))
