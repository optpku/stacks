module

public import ReasLib.Algebra.PowerSums
import StacksCheckRecall

@[expose] public section

/- Lemma 9.13.2 (Tag 0EM9): for a nonempty finite family of pairwise distinct elements of a
field, some power sum is nonzero. The owner works more generally over any commutative domain. -/
@[stacks 0EM9]
#check PowerSums.existsExponentSumNeZero
