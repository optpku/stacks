module

public import ReasLib.RingTheory.Depth
import StacksCheckRecall

/-!
# Definition 10.72.1

@stack 00LI
-/

@[expose] public section

/- Definition 10.72.1: for a finite `R`-module `M`, the `I`-depth of `M` is `∞` when `IM = M`,
and otherwise it is the supremum of the lengths of `M`-regular sequences contained in `I`.

In the local case, the depth of `M` is the depth with respect to the maximal ideal.

Owner: `Ideal.depth`, `Ideal.regularSequenceLengths`, `moduleDepth` in
`ReasLib.RingTheory.Depth`. -/
@[stacks 00LI]
#check @Ideal.depth
@[stacks 00LI "regular-sequence lengths"]
#check @Ideal.regularSequenceLengths
@[stacks 00LI "local module depth"]
#check @moduleDepth
