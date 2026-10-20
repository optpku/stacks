module

import ReasLib.RingTheory.PowerSeries.FractionRing
import Mathlib.NumberTheory.Padics.PadicIntegers
import StacksCheckRecall

@[expose] public section

variable {ℓ : ℕ} [Fact ℓ.Prime]

/- Remark 64.20.3. Since only some theory of traces, rather than determinants, has
been developed, Theorem 64.20.1 is harder to prove than Theorem 64.20.2. Only the
latter is proved here; for the former see SGA4.5. A version with ℤ_[ℓ] coefficients
adds no generality because there is no ℓ-torsion in the coefficient ring.

The checked algebraic content is equality reflection after the canonical map to
ℚ_[ℓ], once both integral power series exist. It constructs neither integral
determinant expressions nor a new cohomological formula. -/
@[stacks 03V1] #check (PowerSeries.map_fractionRing_eq_iff :
  ∀ (f g : PowerSeries ℤ_[ℓ]),
    PowerSeries.map (algebraMap ℤ_[ℓ] ℚ_[ℓ]) f =
      PowerSeries.map (algebraMap ℤ_[ℓ] ℚ_[ℓ]) g ↔ f = g)
