/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DirectLimit.Algebra.Tail.BaseChange.FiniteType
import StacksCheckRecall

/-!
@stack 07RG
-/

@[expose] public section

/- Lemma 10.168.3 [stacks 07RG]: canonical recall.  The reusable owner is
`Ring.DirectLimit.Algebra.Tail.BaseChange.FiniteType.exists_finite`, the
cofinal-tail adapter over the fixed-base core API. -/
@[stacks 07RG]
#check @Ring.DirectLimit.Algebra.Tail.BaseChange.FiniteType.exists_finite
