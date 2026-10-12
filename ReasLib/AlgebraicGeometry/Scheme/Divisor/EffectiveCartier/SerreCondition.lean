/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Depth
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Noetherian
import Mathlib.Tactic.CrossRefAttribute

/-!
# Serre conditions for effective Cartier divisors

This file relates Serre conditions on a locally Noetherian scheme to those on an effective
Cartier divisor.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- An effective Cartier divisor on a locally Noetherian scheme satisfying `(S_k)` satisfies
`(S_{k - 1})`. -/
@[stacks 0B3R]
theorem satisfiesSerreConditionS_subscheme_pred_of_isEffectiveCartierDivisor
    (D : X.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι] (k : ℕ)
    (hX : X.satisfiesSerreConditionS k) :
    D.subscheme.satisfiesSerreConditionS (k - 1) := sorry

end AlgebraicGeometry.Scheme
