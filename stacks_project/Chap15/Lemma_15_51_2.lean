/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.FormalFiber.LocalCriterion
import StacksCheckRecall

/-!
# Lemma 15.51.2

@stack 0BK8
-/

@[expose] public section

/- Lemma 15.51.2, tag `0BK8`: for a local field-algebra property and a ring map with
Noetherian target, testing every fiber is equivalent to testing all prime-local fibers or only
the maximal-local fibers. -/
@[stacks 0BK8 "local criterion for fiber properties"]
#check @FieldAlgebraProperty.fiber_tfae
