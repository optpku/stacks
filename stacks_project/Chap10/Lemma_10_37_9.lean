module

import StacksCheckRecall
public import ReasLib.RingTheory.PowerSeries.Normal

@[expose] public section

/-!
# Normal Formal Power Series Rings

This source-facing file recalls the canonical Noetherian and normality facts
for formal power series over a Noetherian normal domain.

@stack 0BI0
-/

-- Lemma 10.37.9 (Noetherian part): `R⟦X⟧` is Noetherian when `R` is Noetherian.
@[stacks 0BI0 "Noetherian formal power series ring"]
#check @PowerSeries.instIsNoetherianRing

-- Lemma 10.37.9 (normal part), tag `0BI0`: normality is `IsIntegrallyClosed R⟦X⟧`.
@[stacks 0BI0 "formal power series over a normal domain are integrally closed"]
#check @PowerSeries.instIsIntegrallyClosed
