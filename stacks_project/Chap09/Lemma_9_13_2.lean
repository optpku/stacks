/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.PowerSums
import StacksCheckRecall

@[expose] public section

/- Lemma 9.13.2 (Tag 0EM9): for a nonempty finite family of pairwise distinct elements of a
field, some power sum is nonzero. The owner works more generally over any commutative domain. -/
@[stacks 0EM9]
#check PowerSums.existsExponentSumNeZero
