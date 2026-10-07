module

public import ReasLib.RingTheory.AdicCompletion.AnalyticallyUnramified.AtPrime
import StacksCheckRecall

@[expose] public section

/-!
# Associated Primes of Completed Prime Quotients

@stack 032Z

This source-facing entry recalls the reusable completed-localization criterion
for analytically unramified prime quotients.
-/

-- Lemma 10.162.11, tag `032Z`: an associated-prime localization of the
-- completed quotient of an analytically unramified prime is a discrete
-- valuation ring whenever the corresponding source localization is one.
@[stacks 032Z "completed quotient reducedness"]
#check @PrimeSpectrum.IsAnalyticallyUnramified.completionQuotient_isReduced
@[stacks 032Z]
#check @PrimeSpectrum.IsAnalyticallyUnramified.exists_discreteValuationRing_of_completionAssociatedPrime
