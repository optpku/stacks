module

public import ReasLib.RingTheory.Henselian.Product
import StacksCheckRecall

/-!
# Products of henselian pairs

The component theorem, product instance, and source equivalence are owned by `ReasLib`; this file
is the labeled chapter recall.

@stack 0ATD
-/

@[expose] public section

/- Lemma 15.11.11: a product pair is henselian if and only if every component pair is
henselian. -/
@[stacks 0ATD]
#check @henselianRing_pi_iff

#check @HenselianRing.of_pi
#check @pi_henselianRing
