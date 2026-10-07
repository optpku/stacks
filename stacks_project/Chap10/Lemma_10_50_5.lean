module

public import ReasLib.RingTheory.Valuation.Characterization
import StacksCheckRecall

@[expose] public section

/-!
# Valuation subrings of a field

@stack 052K

The canonical data owner is `ValuationSubring.ofSubring`; the source conclusion is exposed as two
atomic `Subring` bridges so downstream code can use either typeclass fact independently.
-/

/- Lemma 10.50.5 (1): the subring is a valuation ring. -/
@[stacks 052K "(1), valuation ring"]
#check @Subring.valuationRing_of_mem_or_inv_mem

/- Lemma 10.50.5 (2): the ambient field is the fraction field of the subring. -/
@[stacks 052K "(2), fraction field"]
#check @Subring.isFractionRing_of_mem_or_inv_mem

@[stacks 052K "canonical valuation-subring data"]
#check @ValuationSubring.ofSubring
