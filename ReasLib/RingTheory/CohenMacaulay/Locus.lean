module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.CohenMacaulay.Module.Local
public import ReasLib.RingTheory.Ideal.MinimalPrime.Localization

@[expose] public section

/-!
# Cohen--Macaulay loci

This leaf owns the pointwise Cohen--Macaulay locus of an affine spectrum.  It
uses the local self-module predicate directly: requiring a global
`CohenMacaulayRing` instance here would be stronger than membership in the
locus and would make the API unusable for singular rings.
-/

universe u v

namespace PrimeSpectrum

section

variable (R : Type u) [CommRing R] [IsNoetherianRing R]

/-- The Cohen--Macaulay locus of `Spec(R)`, consisting of primes whose local rings are
Cohen--Macaulay as self-modules. -/
@[stacks 00RF "Cohen-Macaulay locus"]
def cohenMacaulayLocus : Set (PrimeSpectrum R) :=
  {p | Module.CohenMacaulay (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal)}

/-- Membership in `cohenMacaulayLocus R` is Cohen--Macaulayness of the local ring at the
corresponding prime. -/
@[stacks 00RF "membership in the Cohen-Macaulay locus"]
lemma mem_cohenMacaulayLocus (p : PrimeSpectrum R) :
    p ∈ cohenMacaulayLocus R ↔
      Module.CohenMacaulay (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal) := sorry

attribute [simp] mem_cohenMacaulayLocus

end

end PrimeSpectrum

namespace Module.CohenMacaulay

variable {R : Type u} [CommRing R]

/-- The localization of a Noetherian ring at a minimal prime is Cohen--Macaulay
as a module over itself. -/
@[stacks 00RG "Cohen-Macaulay localization at a minimal prime"]
theorem self_atPrime_of_minimalPrime [IsNoetherianRing R]
    (p : minimalPrimes R) :
    Module.CohenMacaulay (Localization.AtPrime p.1) (Localization.AtPrime p.1) := sorry

end Module.CohenMacaulay

namespace PrimeSpectrum

variable {R : Type u} [CommRing R]

/-- Every minimal prime belongs to the Cohen--Macaulay locus. -/
@[stacks 00RG "minimal primes lie in the Cohen-Macaulay locus"]
theorem mem_cohenMacaulayLocus_of_minimalPrime [IsNoetherianRing R]
    (p : PrimeSpectrum R) (hp : p.asIdeal ∈ minimalPrimes R) :
    p ∈ cohenMacaulayLocus R := sorry

/-- Over a Noetherian ring, the Cohen--Macaulay locus is dense. -/
@[stacks 00RG "density of the Cohen-Macaulay locus"]
theorem dense_cohenMacaulayLocus [IsNoetherianRing R] :
    Dense (cohenMacaulayLocus R) := sorry

end PrimeSpectrum

namespace PrimeSpectrum

section

variable {k : Type u} [Field k]
variable {S : Type v} [CommRing S] [a : Algebra k S] [hfinite : Algebra.FiniteType k S]

include a hfinite

/-- The Cohen--Macaulay locus of a finite-type algebra over a field is open. -/
@[stacks 00RF "openness of the Cohen-Macaulay locus"]
lemma isOpen_cohenMacaulayLocus_of_finiteType
    (hS : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S) :
    -- Local instance justification (defeq pin): `hS` fixes the Noetherian instance used to form the locus.
    letI := hS
    IsOpen (cohenMacaulayLocus S) := sorry

end

end PrimeSpectrum
