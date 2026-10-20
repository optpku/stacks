/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.Completeness.KernelCriterion
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.96.5
@stack 0318
-/

/- Lemma 10.96.5: the `I`-adic completion `AdicCompletion I M` is `I`-adically complete if and
only if, for every positive integer `n`, the kernel of the canonical projection
`AdicCompletion I M → M ⧸ (I ^ n • ⊤)` is exactly `I ^ n` times the completed module. -/
@[stacks 0318]
#check @AdicCompletion.isAdicComplete_iff_ker_eval_eq_pow_smul_top

@[stacks 0318 "completion bijectivity criterion"]
#check @AdicCompletion.of_bijective_iff

@[stacks 0318 "evaluation kernel lower bound"]
#check @AdicCompletion.pow_smul_top_le_ker_eval

end
