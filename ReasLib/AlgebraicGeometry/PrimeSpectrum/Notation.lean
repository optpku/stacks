module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Textbook notation for prime spectra
-/

@[expose] public section

namespace PrimeSpectrum

universe u

variable {R : Type u} [CommSemiring R]

/-- Textbook notation for the basic open of `Spec(R)` on which `f` does not vanish. -/
scoped[PrimeSpectrum] notation "D(" f ")" => basicOpen f

/-- Textbook notation for the zero locus in `Spec(R)` of a set of elements. -/
scoped[PrimeSpectrum] notation "V(" T ")" => zeroLocus T

/-- Membership in `V(T)` means that the prime ideal contains `T`. -/
@[stacks 00DZ]
theorem mem_V (T : Set R) (p : PrimeSpectrum R) :
    p ∈ V(T) ↔ T ⊆ p.asIdeal :=
  PrimeSpectrum.mem_zeroLocus p T

/-- Membership in `D(f)` means that the prime ideal does not contain `f`. -/
@[stacks 00DZ]
theorem mem_D (f : R) (p : PrimeSpectrum R) :
    p ∈ D(f) ↔ f ∉ p.asIdeal :=
  PrimeSpectrum.mem_basicOpen f p

end PrimeSpectrum
