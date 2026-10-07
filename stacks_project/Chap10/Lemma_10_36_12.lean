module

public import ReasLib.RingTheory.IntegralClosure.Local
import StacksCheckRecall

@[expose] public section

/-!
Lemma 10.36.12 (Tag 034K): integrality is local on the prime spectrum.

@stack 034K
-/

-- Lemma 10.36.12: integrality of an element is detected after localization at
-- every prime of the base ring.
@[stacks 034K]
#check @IsIntegral.iff_forall_atPrime
