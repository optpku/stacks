module

public import ReasLib.RingTheory.Henselian.LargestIdeal
import StacksCheckRecall

/-!
# The largest henselian ideal

The concrete supremum and its universal property are owned by `ReasLib`; this file is the labeled
chapter recall.

@stack 0G1S
-/

@[expose] public section

/- Lemma 15.11.15: there exists a largest ideal `I` such that `(A, I)` is a henselian pair. -/
@[stacks 0G1S]
#check @exists_largest_henselianIdeal

#check @largestHenselianIdeal
#check @le_largestHenselianIdeal
