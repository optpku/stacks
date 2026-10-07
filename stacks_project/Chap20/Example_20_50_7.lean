module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Duality
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived

variable {X : RingedSpace.{u}}
variable [KFlat.HomotopyTensorDescends X] [KFlat.TensorDescends X]
variable [KFlat.IsLocalization X]
variable [MonoidalClosed (ModuleDerived X)]

/- Example 20.50.7: perfectness supplies the invertibility criterion for the canonical
closed-monoidal pairing of `K` with `MonoidalClosed.dual K`. -/
@[stacks 0FPC]
#check fun {K : ModuleDerived X} (hK : IsPerfect K) ↦
  hK.isRightDualizable.isIso_tensorIhomUnitToEnd

/- The concrete pairing data are owned generically.  In source order they form
`ExactPairing K (MonoidalClosed.dual K)`, with coevaluation into
`K ⊗ MonoidalClosed.dual K`. -/
#check @MonoidalClosed.Dual.exactPairing
#check @MonoidalClosed.Dual.coevaluation
#check @MonoidalClosed.Dual.evaluation
#check @MonoidalClosed.Dual.coevaluation_comp_tensorComparison
#check @MonoidalClosed.Dual.exactPairing_coevaluation
#check @MonoidalClosed.Dual.exactPairing_evaluation
#check @ExactPairing.coevaluation_evaluation
#check @ExactPairing.evaluation_coevaluation

end AlgebraicGeometry.RingedSpace.ModuleDerived
