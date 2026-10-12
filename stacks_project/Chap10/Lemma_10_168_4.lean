/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DirectLimit.Algebra.Tail.BaseChange.FiniteType
import StacksCheckRecall

/-!
# Lemma 10.168.4

@stack 07RH
-/

@[expose] public section

/- Lemma 10.168.4 [stacks 07RH]: canonical recall.  The reusable owner is
`Ring.DirectLimit.Algebra.Tail.BaseChange.FiniteType.exists_surjective`, the
cofinal-tail adapter over the fixed-base core API. -/
@[stacks 07RH]
#check @Ring.DirectLimit.Algebra.Tail.BaseChange.FiniteType.exists_surjective
