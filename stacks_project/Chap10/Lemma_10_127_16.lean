/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.Existence
import StacksCheckRecall

/-!
# Lemma 10.127.16

@stack 00QZ
-/

@[expose] public section

/- Lemma 10.127.16 [stacks 00QZ]: canonical recall. The reusable owner is
`Ring.DirectLimit.Algebra.Approximation.FiniteType.exists_of_finiteType`; it
adds surjective stagewise base-change maps to a directed finite-type
approximation of an arbitrary finite-type commutative ring map. -/
@[stacks 00QZ]
#check @Ring.DirectLimit.Algebra.Approximation.FiniteType.exists_of_finiteType
