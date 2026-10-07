module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.AlmostIntegral
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

universe u v

namespace PowerSeries

/-- Lemma 110.12.5: if `R` is a domain with fraction field `K` and
`PowerSeries R` is flat over `Polynomial R`, then `R` is integrally closed
if and only if `completeIntegralClosure R K = ⊥`. -/
@[stacks 0F1Y]
theorem isIntegrallyClosed_iff_completeIntegralClosure_eq_bot
    {R : Type u} {K : Type v} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (h_flat : Module.Flat (Polynomial R) (PowerSeries R)) :
    IsIntegrallyClosed R ↔ completeIntegralClosure R K = ⊥ := sorry

end PowerSeries
