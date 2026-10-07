module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.PowerSeries.Basic

@[expose] public section

universe u

namespace PowerSeries

/-- There exists a commutative ring `R` whose formal power series ring is not
flat over `R` and is not flat over the polynomial ring over `R`. -/
theorem exists_notFlat :
    ∃ (R : Type u) (_ : CommRing R),
      ¬ Module.Flat R (PowerSeries R) ∧
        ¬ Module.Flat (Polynomial R) (PowerSeries R) := sorry

end PowerSeries
