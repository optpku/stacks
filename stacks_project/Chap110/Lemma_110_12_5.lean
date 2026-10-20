module

public import ReasLib.RingTheory.PowerSeries.Normal
import StacksCheckRecall

@[expose] public section

universe u v

/- Lemma 110.12.5: if `R` is a domain with fraction field `K` and
`PowerSeries R` is flat over `Polynomial R`, then `R` is integrally closed
if and only if `completeIntegralClosure R K = ⊥`. -/
@[stacks 0F1Y] #check (PowerSeries.isIntegrallyClosed_iff_completeIntegralClosure_eq_bot :
    ∀ {R : Type u} {K : Type v} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
      [IsFractionRing R K], Module.Flat (Polynomial R) (PowerSeries R) →
        (IsIntegrallyClosed R ↔ completeIntegralClosure R K = ⊥))
