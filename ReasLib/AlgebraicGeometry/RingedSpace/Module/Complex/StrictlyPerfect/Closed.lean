/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Complex.StrictlyPerfect.Dualizable
public import ReasLib.CategoryTheory.Monoidal.Closed.Dualizable
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Closed duality for locally strictly perfect complexes

This companion connects the monoidal dualizability criterion to a chosen closed structure.
Concrete dual, evaluation, coevaluation, and exact-pairing data remain owned by the generic
`MonoidalClosed.Dual` namespace.
-/

open CategoryTheory

universe u

namespace AlgebraicGeometry.RingedSpace.CochainComplex

variable {X : RingedSpace.{u}}

/-- Local strict perfectness makes the canonical tensor-to-endomorphism comparison invertible. -/
@[stacks 0FP9 "closed comparison criterion"]
theorem IsLocallyStrictlyPerfect.isIso_tensorIhomUnitToEnd
    {F : _root_.CochainComplex (Modules X) ℤ}
    (hF : IsLocallyStrictlyPerfect F) :
    IsIso (MonoidalClosed.tensorIhomUnitToEnd F) := sorry

end AlgebraicGeometry.RingedSpace.CochainComplex
