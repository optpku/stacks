module

import StacksCheckRecall
public import ReasLib.RingTheory.Sequence.QuasiRegular.Basic

/-!
# Definition 10.69.1

@stack 061P
-/

@[expose] public section

/- Definition 10.69.1, tag `061P`: the module-valued quasi-regularity owner
is provided by the shared associated-graded comparison API. -/
@[stacks 061P "quasi-regular sequences"]
#check @RingTheory.Sequence.IsQuasiRegular

/- Companion API for Definition 10.69.1: the canonical comparison map. -/
@[stacks 061P "associated-graded comparison map"]
#check @RingTheory.Sequence.QuasiRegular.comparisonMap

/- Companion API for Definition 10.69.1: quasi-regularity may be checked by
injectivity because the comparison map is always surjective. -/
@[stacks 061P "quasi-regularity criterion"]
#check @RingTheory.Sequence.isQuasiRegular_iff_injective

/- Companion API for Definition 10.69.1: a quasi-regular sequence gives the
canonical polynomial-linear equivalence. -/
@[stacks 061P "quasi-regular comparison equivalence"]
#check @RingTheory.Sequence.IsQuasiRegular.linearEquiv

/- Companion API for Definition 10.69.1: the ring-valued specialization. -/
@[stacks 061P "quasi-regular sequences"]
#check @RingTheory.Sequence.IsQuasiRegularSequence
