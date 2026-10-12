/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.DerivedCategory.TruncationSplitting
import StacksCheckRecall

@[expose] public section

/- Lemma 13.27.10: uniform vanishing of `Ext B A 2` yields the finite shifted-cohomology
decomposition of every bounded derived object. -/
@[stacks 0EWX] #check @DerivedCategory.ShiftedCohomology.Split.ofExtTwo
