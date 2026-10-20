/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Etale.LocalCriterion
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.143.7

@stack 00U6

The source-facing recall keeps the prime `p` and the selected prime `q`
explicit.  The contraction-based form is exposed as an untagged companion
for consumers whose local data are already phrased at `q.under R`.
-/

@[stacks 00U6]
#check @Algebra.IsEtaleAt.of_flat_over_of_maximalIdeal_of_separable

@[stacks 00U6 "contraction-based etale criterion"]
#check @Algebra.IsEtaleAt.of_flat_of_maximalIdeal_of_separable
