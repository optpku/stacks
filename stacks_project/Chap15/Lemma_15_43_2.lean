/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Completion.Depth
import StacksCheckRecall

/-!
# Lemma 15.43.2 (07NW)

@stack 07NW
-/

@[expose] public section

/- Lemma 15.43.2 (07NW): depth is preserved by maximal-ideal completion. -/
@[stacks 07NW]
#check @AdicCompletion.moduleDepth_eq
