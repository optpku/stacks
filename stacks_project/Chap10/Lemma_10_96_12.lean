/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.AdicCompletion.Finite
import StacksCheckRecall

@[expose] public section

/-!
@stack 031D
# Lemma 10.96.12

The finite-quotient criterion is owned by
`ReasLib.RingTheory.AdicCompletion.Finite`, including the source-faithful
complete-ring specialization.
-/

/- Lemma 10.96.12: if `R` is `I`-adically complete, the reduction of `M`
modulo `I` is finite, and the adic intersection vanishes, then `M` is finite. -/
@[stacks 031D]
#check @Module.Finite.of_quotient_of_ringComplete_of_iInf_pow_smul_eq_bot

/- Weaker ring-side precompleteness companions. -/
#check @Module.Finite.of_quotient_of_iInf_pow_smul_eq_bot
#check @Module.Finite.of_quotient_of_isHausdorff
