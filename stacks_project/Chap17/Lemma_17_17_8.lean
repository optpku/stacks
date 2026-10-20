module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Flat.Exact
import StacksCheckRecall

@[expose] public section

/- Lemma 17.17.8 (05NJ): tensoring a short exact sequence on the right preserves exactness when
the quotient is flat. -/
@[stacks 05NJ]
#check @SheafOfModules.RingedSite.shortExact_tensor_right_of_flat_quotient
