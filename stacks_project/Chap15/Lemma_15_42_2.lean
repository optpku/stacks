/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Regular.Normal
import StacksCheckRecall

/-!
# Lemma 15.42.2 (0BFK)

@stack 0BFK
-/

@[expose] public section

/- Lemma 15.42.2 (0BFK): normality ascends along a regular ring map between Noetherian rings. -/
@[stacks 0BFK]
#check @RingHom.Regular.isNormalRing
