module

public import ReasLib.RingTheory.Flat.FaithfullyFlat.Projective
import StacksCheckRecall

@[expose] public section

/-!
# Theorem 10.95.6

@stack 05A9
-/

/- Theorem 10.95.6 [stacks 05A9]: canonical recall of faithfully flat descent
of projectivity for arbitrary modules. -/
@[stacks 05A9]
#check @Module.Projective.of_tensorProduct
