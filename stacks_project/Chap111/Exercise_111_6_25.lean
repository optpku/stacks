module

public import Mathlib.RingTheory.Spectrum.Prime.Basic
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

universe u

namespace PrimeSpectrum

/-- Exercise 111.6.25: for ideals `I` and `J` of a commutative semiring `R`, the closed sets
`V(I)` and `V(J)` in `PrimeSpectrum R` are disjoint if and only if `I ⊔ J = ⊤`, equivalently
`I + J` is the unit ideal. -/
@[stacks 02DF]
theorem disjoint_zeroLocus_iff {R : Type u} [CommSemiring R] (I J : Ideal R) :
    Disjoint (zeroLocus (I : Set R)) (zeroLocus (J : Set R)) ↔ I ⊔ J = ⊤ := sorry

end PrimeSpectrum

/- Companion: `zeroLocus (I ⊔ J) = zeroLocus I ∩ zeroLocus J`. -/
#check @PrimeSpectrum.zeroLocus_sup

/- Companion: `zeroLocus K = ∅` if and only if `K` is the unit ideal. -/
#check @PrimeSpectrum.zeroLocus_empty_iff_eq_top

/- Companion: `IsCoprime I J` if and only if `I ⊔ J = ⊤`. -/
#check @Ideal.isCoprime_iff_sup_eq
