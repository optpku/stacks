/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.KrullDimension.FiniteType.ZeroDimensional
import StacksCheckRecall

@[expose] public section

/-!
# A regular nonunit in a positive-dimensional finite-type algebra

@stack 0GEC
-/

/- Lemma 10.63.20: recall the reusable positive-dimensional finite-type algebra
existence theorem for a non-zero-divisor that is not a unit. -/
@[stacks 0GEC]
#check @Algebra.FiniteType.exists_nonZeroDivisor_nonunit_of_pos_ringKrullDim
