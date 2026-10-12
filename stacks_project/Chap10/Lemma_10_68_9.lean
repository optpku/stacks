/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Sequence.Regularity.Power
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.68.9

@stack 07DV

The source statement is kept as a list-level bridge.  The regular-sequence
predicate and its append/power primitives are owned by Mathlib/ReasLib; the
induction and quotient transport belong to the proof stage.
-/

/- Lemma 10.68.9: positive entrywise powers preserve and reflect regularity. -/
@[stacks 07DV]
#check @RingTheory.Sequence.isRegular_iff_isRegular_pow
