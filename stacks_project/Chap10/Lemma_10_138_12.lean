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
