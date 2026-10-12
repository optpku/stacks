/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Complex.StrictlyPerfect.Closed
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory

universe u

namespace AlgebraicGeometry.RingedSpace.CochainComplex

variable {X : RingedSpace.{u}}

/- Example 20.50.2: a locally strictly perfect complex is dualizable for the canonical total
tensor product. -/
@[stacks 0FP9]
#check fun {F : _root_.CochainComplex (Modules X) ℤ}
    (hF : IsLocallyStrictlyPerfect F) ↦
  hF.isRightDualizable

section Closed

/- For a closed structure, dualizability makes the canonical tensor-to-endomorphism comparison
invertible; the generic owner then supplies the concrete internal-Hom dual, evaluation,
coevaluation, and triangle identities. -/
#check fun {F : _root_.CochainComplex (Modules X) ℤ}
    (hF : IsLocallyStrictlyPerfect F) ↦
  hF.isIso_tensorIhomUnitToEnd
#check @MonoidalClosed.Dual.exactPairing
#check @MonoidalClosed.Dual.coevaluation
#check @MonoidalClosed.Dual.evaluation
#check @ExactPairing.coevaluation_evaluation
#check @ExactPairing.evaluation_coevaluation

end Closed

end AlgebraicGeometry.RingedSpace.CochainComplex
