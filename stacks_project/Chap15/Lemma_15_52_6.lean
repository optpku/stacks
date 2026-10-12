/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.FormalFiber.Normal
import StacksCheckRecall

/-!
# Lemma 15.52.6

@stack 0C23
-/

@[expose] public section

/- Lemma 15.52.6: a normal Noetherian local ring with normal formal fibers has normal
maximal-ideal completion. -/
@[stacks 0C23]
#check @IsNormalRing.adicCompletion_of_formalFibers
