module

public import ReasLib.RingTheory.AdicCompletion.Finite
import StacksCheckRecall

@[expose] public section

/-!
@stack 031B
# Lemma 10.96.11

The finite-module completeness API is owned by
`ReasLib.RingTheory.AdicCompletion.Finite`, including the source-faithful
complete-ring specialization.
-/

/- Lemma 10.96.11: if `R` is `I`-adically complete, `M` is a finite
`R`-module, and the adic intersection is zero, then `M` is complete. -/
@[stacks 031B]
#check @IsAdicComplete.of_finite_of_ringComplete_of_iInf_pow_smul_eq_bot

/- Weaker ring-side precompleteness companion. -/
@[stacks 031B "ring-side adic completeness companion"]
#check @IsAdicComplete.of_finite_of_iInf_pow_smul_eq_bot
