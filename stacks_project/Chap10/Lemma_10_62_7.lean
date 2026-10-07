module

public import ReasLib.RingTheory.Module.SupportDim
import StacksCheckRecall

/-!
# Support dimension in a short exact sequence

@stack 0B51
-/

@[expose] public section

/- Lemma 10.62.7: in a short exact sequence, the support dimension of the middle term is the
maximum of the endpoint support dimensions.  The reusable owner needs neither Noetherianity nor
finite generation; symmetry of equality gives the source orientation. -/
@[stacks 0B51]
#check @Module.supportDim_eq_max_of_shortExact
