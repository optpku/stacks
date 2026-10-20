module

public import ReasLib.RingTheory.PowerSeries.Valuation
public import ReasLib.RingTheory.Coherent.Valuation
public import ReasLib.RingTheory.Flatness.MittagLeffler.PowerSeries
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 110.12.6: if `R` is a valuation ring of Krull dimension greater than one,
then `PowerSeries R` is flat over `R` but not over `Polynomial R`. -/
@[stacks 0F1Z] #check (PowerSeries.not_flat_polynomial :
  ∀ {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R],
    1 < ringKrullDim R → ¬ Module.Flat (Polynomial R) (PowerSeries R))

variable {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R]

/- Lemma 110.12.6 (1): formal power series over a valuation ring are flat over
the coefficient ring, without a dimension hypothesis. -/
@[stacks 0F1Z] #check (Module.Flat.mvPowerSeries : Module.Flat R (PowerSeries R))
