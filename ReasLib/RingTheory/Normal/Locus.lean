module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Normal.Ring

@[expose] public section

/-!
# Normal Locus

This leaf owns the normal locus of an affine prime spectrum.  It is defined
pointwise from `IsNormalRing` of the prime localization, so it applies to an
arbitrary commutative ring rather than only to domains or Noetherian rings.
The domain and Noetherian hypotheses enter only in the openness criteria.
-/

universe u

namespace PrimeSpectrum

section

variable (R : Type u) [CommRing R]

/-- The normal locus of `Spec(R)`, consisting of primes whose local rings are
normal. -/
@[stacks 0332 "normal locus"]
def normalLocus : Set (PrimeSpectrum R) :=
  {p | IsNormalRing (Localization.AtPrime p.asIdeal)}

/-- Membership in `normalLocus R` is normality of the local ring at the
corresponding prime. -/
@[stacks 0332 "membership in the normal locus"]
lemma mem_normalLocus (p : PrimeSpectrum R) :
    p ∈ normalLocus R ↔ IsNormalRing (Localization.AtPrime p.asIdeal) := sorry

attribute [simp] mem_normalLocus

end

section

variable {R : Type u} [CommRing R] [IsDomain R]

/-- Over a domain, membership in the normal locus is equivalent to integral
closedness of the corresponding prime localization. -/
@[stacks 0332 "domain description of the normal locus"]
lemma mem_normalLocus_iff_isIntegrallyClosed (p : PrimeSpectrum R) :
    p ∈ normalLocus R ↔ IsIntegrallyClosed (Localization.AtPrime p.asIdeal) := sorry

end

namespace NormalLocus

/-- Lemma 10.161.14, tag `0332`: the normal locus of a Noetherian domain is
open when one nonzero principal localization is normal. -/
@[stacks 0332]
theorem isOpen_of_exists_normal_localizationAway
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (h : ∃ f : R, f ≠ 0 ∧ IsNormalRing (Localization.Away f)) :
    IsOpen (normalLocus R) := sorry

/-- Domain companion to Lemma 10.161.14: integral closedness of one nonzero
principal localization also makes the normal locus open. -/
@[stacks 0332 "integrally closed companion"]
theorem isOpen_of_exists_integrallyClosed_localizationAway
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (h : ∃ f : R, f ≠ 0 ∧ IsIntegrallyClosed (Localization.Away f)) :
    IsOpen (normalLocus R) := sorry

end NormalLocus

end PrimeSpectrum
