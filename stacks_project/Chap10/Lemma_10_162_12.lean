module

public import ReasLib.RingTheory.AdicCompletion.AnalyticallyUnramified.AssociatedPrime
import StacksCheckRecall

@[expose] public section

/-!
# Principal-Quotient Criterion for Analytic Unramifiedness

@stack 0330

This source-facing entry recalls the associated-prime criterion for a
Noetherian local domain to be analytically unramified.
-/

-- Lemma 10.162.12, tag `0330`: a nonzero principal quotient without embedded
-- primes, whose associated-prime localizations are regular and analytically
-- unramified, makes the source local domain analytically unramified.
@[stacks 0330]
#check @IsAnalyticallyUnramified.of_principalQuotient_associatedPrimes
