/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Smooth.Quotient
import StacksCheckRecall

@[expose] public section

/-!
@stack 031L
-/

/- Lemma 10.138.12 [stacks 031L]: canonical recall of square-zero quotient
ascent for formally smooth algebras. -/

@[stacks 031L]
#check @Algebra.FormallySmooth.of_squareZeroIdeal_of_flat
