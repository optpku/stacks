module

public import ReasLib.FieldTheory.Transcendence.PurelyTranscendental
public import ReasLib.NumberTheory.Transcendental.LindemannWeierstrass
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
import StacksCheckRecall

@[expose] public section

open IntermediateField
open IntermediateField.AdjoinSimple
open FieldExtension
open scoped RatFunc

/-!
Example 9.26.2 (Tag 09I8): the simple extension `ℚ(π)` is a one-variable purely transcendental
extension of `ℚ`. The input `Real.pi` is transcendental by the reusable Lindemann-Weierstrass API.
-/

#check LindemannWeierstrass.exp_ne_neg_one_of_isAlgebraic_ne_zero
#check real_pi_transcendental

/-- Example 9.26.2: the simple extension `ℚ(π)` is purely transcendental over `ℚ`. -/
@[stacks 09I8]
theorem rat_adjoin_pi_isPurelyTranscendental :
    IsPurelyTranscendental ℚ ℚ⟮Real.pi⟯ :=
  isPurelyTranscendental_adjoin_simple_of_transcendental real_pi_transcendental

noncomputable section

section

-- Local instance justification (defeq pin): use the polynomial-induced algebra on `RatFunc ℚ` required by `RatFunc.algEquivOfTranscendental`.
local instance ratFuncRatAlgebra : Algebra ℚ (RatFunc ℚ) :=
  RatFunc.instAlgebraOfPolynomial ℚ ℚ

/- The canonical rational-function-field presentation is already owned by
`RatFunc.algEquivOfTranscendental`; no source-local alias is needed. -/
#check (RatFunc.algEquivOfTranscendental Real.pi real_pi_transcendental :
  RatFunc ℚ ≃ₐ[ℚ] ℚ⟮Real.pi⟯)

end
