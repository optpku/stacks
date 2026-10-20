/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.AdicCompletion.Completeness
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.96.3

@stack 05GG
-/

/-!
# Finitely generated adic completion

Lemma 10.96.3, tag `05GG`, is owned by Mathlib's generic adic-completion API.
The ring-specific completion kernel bridge belongs in
`ReasLib.RingTheory.AdicCompletion.Congruence` rather than this source recall.
-/

/- Lemma 10.96.3 (1), tag `05GG`: a finitely generated adic completion is
adically complete. -/
@[stacks 05GG "(1)"]
#check @AdicCompletion.isAdicComplete

/- Lemma 10.96.3 (2), tag `05GG`: `I ^ n • ⊤` is the kernel of the stage-`n`
evaluation map. -/
@[stacks 05GG "(2)"]
#check @AdicCompletion.pow_smul_top_eq_ker_eval

/- Lemma 10.96.3 (2), tag `05GG`: completion of `I ^ n M` realizes the same
kernel after restricting scalars. -/
@[stacks 05GG "(2)"]
#check @AdicCompletion.restrictScalars_range_ofPowSMul_eq_ker_eval
