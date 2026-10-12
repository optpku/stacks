/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.ClosedPointFiber.Visible
import StacksCheckRecall

/-!
# Lemma 15.128.2 (0GV9)

The canonical short exact sequence defining `V(x)` and the localized splitting criterion are owned
by `ReasLib.Algebra.Module.ClosedPointFiber.Visible`.

@stack 0GV9
-/

@[expose] public section

open scoped ClosedPointFiber

@[stacks 0GV9 "canonical visible-fiber short exact sequence"]
#check @Module.ClosedFiber.shortExact

@[stacks 0GV9 "visible fiber class"]
#check @Module.ClosedFiber.visibleClass

@[stacks 0GV9 "global forms on the visible dual"]
#check @Module.ClosedFiber.visibleLinearForm_surjective

@[stacks 0GV9 "localized splitting and visible-class independence"]
#check @Module.ClosedFiber.selectedSectionsSplitAfterInverting_iff_linearIndependent
