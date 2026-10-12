/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

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

/- Lemma 20.50.8 (1): an object of `D(𝒪_X)` admitting a source-convention left dual,
represented in Mathlib by `IsRightDualizable`, is perfect. -/
@[stacks 0FPD "(1)"]
#check @isPerfect_of_isRightDualizable

/- Explicit source-order pairing data imply the same perfectness statement. -/
#check fun {M N : ModuleDerived X} (p : ExactPairing M N) ↦
  isPerfect_of_isRightDualizable (IsRightDualizable.of_exactPairing p)

section Closed

variable [MonoidalClosed (ModuleDerived X)]

/- Lemma 20.50.8 (2): a chosen source-convention left dual is canonically isomorphic to
the closed-monoidal dual constructed in Example 20.50.7. -/
@[stacks 0FPD "(2)"]
#check fun {M N : ModuleDerived X} (p : ExactPairing M N) ↦
  MonoidalClosed.Dual.rightDualIso p

end Closed

end AlgebraicGeometry.RingedSpace.ModuleDerived
