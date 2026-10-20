module

public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import ReasLib.RingTheory.KrullDimension.DimensionLEOne
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Krull dimension of prime quotients

This leaf relates the Krull dimension of a quotient by a prime ideal to the
coheight of the corresponding point of the prime spectrum.  It is stated at
the `PrimeSpectrum` owner, so downstream dimension arguments do not have to
rebuild the quotient-spectrum comparison.
-/

universe u

namespace PrimeSpectrum

/-- The zero locus of a prime ideal is the upper interval above the corresponding
point of the prime spectrum. -/
@[stacks 00KX "prime zero locus as an upper interval"]
theorem zeroLocus_eq_Ici
    {R : Type u} [CommRing R] (p : PrimeSpectrum R) :
    PrimeSpectrum.zeroLocus p.asIdeal = Set.Ici p := sorry

/-- The prime spectrum of `R ⧸ p` is canonically order-isomorphic to the
upper interval of primes containing `p`.

This composes Mathlib's quotient-spectrum/zero-locus equivalence with `zeroLocus_eq_Ici`; keeping
the order isomorphism as the data owner preserves specialization information for every downstream
dimension and finiteness argument. -/
@[stacks 00KX "prime quotient spectrum as an upper interval"]
noncomputable def quotientOrderIsoIci
    {R : Type u} [CommRing R] (p : PrimeSpectrum R) :
    PrimeSpectrum (R ⧸ p.asIdeal) ≃o Set.Ici p :=
  (Ideal.primeSpectrumQuotientOrderIsoZeroLocus p.asIdeal).trans
    (OrderIso.setCongr _ _ (zeroLocus_eq_Ici p))

/-- The quotient upper-interval equivalence sends a quotient prime to its
contraction along the quotient map. -/
@[simp, stacks 00KX "prime quotient upper-interval comparison on points"]
theorem quotientOrderIsoIci_apply
    {R : Type u} [CommRing R] (p : PrimeSpectrum R)
    (q : PrimeSpectrum (R ⧸ p.asIdeal)) :
    ((quotientOrderIsoIci p q : Set.Ici p) : PrimeSpectrum R) =
      PrimeSpectrum.comap (Ideal.Quotient.mk p.asIdeal) q := sorry

/-- Infinitude of the quotient spectrum is equivalent to infinitude of the
upper interval above the quotient prime. -/
@[stacks 00KX "infinitude of a prime quotient spectrum"]
theorem infinite_quotient_iff_Ici
    {R : Type u} [CommRing R] (p : PrimeSpectrum R) :
    Infinite (PrimeSpectrum (R ⧸ p.asIdeal)) ↔ Infinite (Set.Ici p) := sorry

/-- The dimension-one spectrum comparison is stated as an iff so downstream arguments can choose
the spectrum whose infinitude is already available, without rebuilding a finite/infinite
contradiction locally. -/
@[stacks 00KX "infinite maximal and prime spectra in dimension at most one"]
theorem infinite_maximalSpectrum_iff_infinite_primeSpectrum
    {R : Type u} [CommRing R] [Ring.DimensionLEOne R] :
    Infinite (MaximalSpectrum R) ↔ Infinite (PrimeSpectrum R) := sorry

/-- A basic open whose intersection with the zero locus of `p` is `{p}`
becomes the generic singleton after quotienting by `p`. This is independent of
Noetherian hypotheses. -/
@[stacks 00KX "quotient basic open as generic singleton"]
theorem quotient_basicOpen_eq_singleton_bot
    {R : Type u} [CommRing R] (p : PrimeSpectrum R) (f : R)
    (hp :
      PrimeSpectrum.zeroLocus (R := R) (p.asIdeal : Set R) ∩
        (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) = {p}) :
    (PrimeSpectrum.basicOpen (Ideal.Quotient.mk p.asIdeal f) :
        Set (PrimeSpectrum (R ⧸ p.asIdeal))) =
      ({(⊥ : PrimeSpectrum (R ⧸ p.asIdeal))} : Set (PrimeSpectrum (R ⧸ p.asIdeal))) := sorry

/-- A basic open that is the generic singleton remains so after localizing
at any prime of a domain. -/
@[stacks 00KX "localized basic open as generic singleton"]
theorem localizationAtPrime_basicOpen_eq_singleton_bot
    {A : Type u} [CommRing A] [IsDomain A] {x : A}
    (hbasic :
      (PrimeSpectrum.basicOpen x : Set (PrimeSpectrum A)) =
        ({(⊥ : PrimeSpectrum A)} : Set (PrimeSpectrum A)))
    (q : PrimeSpectrum A) :
    (PrimeSpectrum.basicOpen (algebraMap A (Localization.AtPrime q.asIdeal) x) :
        Set (PrimeSpectrum (Localization.AtPrime q.asIdeal))) =
      ({(⊥ : PrimeSpectrum (Localization.AtPrime q.asIdeal))} :
        Set (PrimeSpectrum (Localization.AtPrime q.asIdeal))) := sorry

/-- In a Noetherian domain, a nonzero prime below a generic singleton basic
open has height one. -/
@[stacks 00KX "height one below a generic singleton basic open"]
theorem height_eq_one_of_basicOpen_eq_singleton_bot
    {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] {x : A}
    (hbasic :
      (PrimeSpectrum.basicOpen x : Set (PrimeSpectrum A)) =
        ({(⊥ : PrimeSpectrum A)} : Set (PrimeSpectrum A)))
    (q : PrimeSpectrum A) (hq : q ≠ ⊥) :
    q.asIdeal.height = 1 := sorry

/-- The Krull dimension of the quotient by a prime ideal is the coheight of the
corresponding point of the prime spectrum. -/
@[stacks 00KX "dimension of a prime quotient"]
theorem ringKrullDim_quotient_eq_coheight
    {R : Type u} [CommRing R] (p : PrimeSpectrum R) :
    ringKrullDim (R ⧸ p.asIdeal) = (Order.coheight p : WithBot ℕ∞) := sorry

end PrimeSpectrum

namespace IsLocalization.AtPrime

/-- The localization at a prime has Krull dimension zero exactly when the prime is minimal. -/
@[stacks 00PJ "zero-dimensional prime localization criterion"]
theorem ringKrullDim_eq_zero_iff_mem_minimalPrimes
    {R : Type u} [CommRing R] (q : PrimeSpectrum R) :
    ringKrullDim (Localization.AtPrime q.asIdeal) = 0 ↔
      q.asIdeal ∈ minimalPrimes R := sorry

end IsLocalization.AtPrime
