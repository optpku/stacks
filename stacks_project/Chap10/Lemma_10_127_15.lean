module

public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.Finite
import StacksCheckRecall

/-!
# Lemma 10.127.15

@stack 0BTG
-/

@[expose] public section

/- Lemma 10.127.15 [stacks 0BTG]: canonical recall. The reusable owner is
`Ring.DirectLimit.Algebra.Approximation.Finite.nonempty_of_integral`; it gives
a directed finite algebra approximation of an arbitrary integral commutative
ring map. -/
@[stacks 0BTG]
#check @Ring.DirectLimit.Algebra.Approximation.Finite.nonempty_of_integral

@[stacks 0BTG "explicit finite approximation constructor"]
#check @Ring.DirectLimit.Algebra.Approximation.Finite.of
