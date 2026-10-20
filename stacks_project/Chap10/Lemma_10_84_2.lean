/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.DirectSumDevissage.SuccessiveQuotient
import StacksCheckRecall

/-!
# Lemma 10.84.2

@stack 058V
-/

@[expose] public section

/- Lemma 10.84.2 (Tag 058V): a direct-sum devissage decomposes its module as the direct sum of
the successive quotients. -/
@[stacks 058V]
#check @DirectSumDevissage.nonempty_linearEquiv_successiveQuotients

/- The canonical index and quotient objects used by the decomposition. -/
@[stacks 058V "successor index"]
#check @DirectSumDevissage.successorIndex

@[stacks 058V "successive quotient"]
#check @DirectSumDevissage.successiveQuotient
