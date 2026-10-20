module

public import ReasLib.RingTheory.Ideal.FlatQuotient
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.17.1

@stack 0524

For an Artinian ring, the flat-quotient ideals form a nonempty descending family with a least
member.  `Ideal.exists_isLeastFlatQuotient` is the reusable lattice-level owner; this file keeps
the textbook entry as a tagged recall and does not recreate the quotient action, predicate, or
minimality argument in the chapter namespace.
-/

/- Lemma 15.17.1 (Stacks `0524`): an Artinian ring has a least flat-quotient ideal. -/
@[stacks 0524 "least ideal with flat quotient over an Artinian ring"]
#check @Ideal.exists_isLeastFlatQuotient

#check @Ideal.top_isFlatQuotient
#check @Ideal.IsFlatQuotient.inf
#check @Ideal.quotientSmulTopModule

end
