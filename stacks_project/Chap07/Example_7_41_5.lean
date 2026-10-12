/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Action.Counterexample

import StacksCheckRecall

@[expose] public section

/-! [stacks 08LS (1)] -/
@[stacks 08LS "(1)"] #check @Action.res_isContinuous

/-! [stacks 08LS (2)] -/
@[stacks 08LS "(2)"] #check @Action.res_isCoverDense_of_injective

/-! [stacks 08LS (3)] -/
@[stacks 08LS "(3)"] #check @CategoryTheory.Action.coinducedEvalOne

/-! [stacks 08LS (4)] -/
@[stacks 08LS "(4)"] #check @CategoryTheory.Action.coinducedEvalOne_surjective_of_injective

/-! [stacks 08LS (5)] -/
@[stacks 08LS "(5)"] #check @CategoryTheory.Action.Counterexample.TwoPoint.evalOne_not_injective

/-! [stacks 08LS (6)] -/
@[stacks 08LS "(6)"] #check @CategoryTheory.Action.Counterexample.TwoPoint.pushforward_not_preservesCoequalizers

/-! [stacks 08LS (7)] -/
@[stacks 08LS "(7)"] #check @CategoryTheory.Action.Counterexample.TwoPoint.pushforward_not_preservesPushouts
