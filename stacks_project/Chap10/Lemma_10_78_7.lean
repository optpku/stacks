module

public import ReasLib.RingTheory.Flatness.LocallyFree.Semilocal
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.78.7
@stack 02M9

The constant-rank criterion is recalled directly from Mathlib.  The connected-spectrum statement
is retained as the source-facing specialization for finite locally free modules over a semilocal
ring.
-/

/- Lemma 10.78.7 (1): constant finite fiber rank implies freeness. -/
@[stacks 02M9 "constant-rank criterion"]
#check @Module.free_of_flat_of_finrank_eq

@[stacks 02M9 "source-facing specialization"]
#check @Module.free_of_semilocal_of_connected_spectrum

end
