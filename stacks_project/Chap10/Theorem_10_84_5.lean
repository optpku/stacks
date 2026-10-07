module

public import ReasLib.RingTheory.Finiteness.Projective.CountablyGenerated
import StacksCheckRecall

/-!
# Kaplansky's theorem for projective modules

@stack 058Y

The countable-generation and projectivity condition on each summand is canonically expressed by
`Module.CountablyGeneratedProjective`. The decomposition itself uses the proposition-facing
`iSupIndep` and `iSup = ⊤` formulation, so it does not expose a chosen `DecidableEq` instance.
-/

@[expose] public section

universe u v w

/- Theorem 10.84.5: the reusable Kaplansky decomposition is owned by the projective-module leaf. -/
@[stacks 058Y]
#check @Module.Projective.exists_countablyGenerated_decomposition
#check @Module.CountablyGeneratedProjective
