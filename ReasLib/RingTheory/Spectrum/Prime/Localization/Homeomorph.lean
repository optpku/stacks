module

public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Spectrum of a localization

This leaf packages the generic homeomorphism from the spectrum of a localization
to the subspace of primes disjoint from the localized submonoid.  The embedding
and range identities remain owned by Mathlib; this module only bundles them and
exposes the forward and inverse prime formulas.

@stack 00E3
-/

@[expose] public section

noncomputable section

universe u

namespace PrimeSpectrum

variable {R : Type u} [CommRing R]

/-- Lemma 10.17.5, tag `00E3`: the spectrum of `Localization M` is homeomorphic
to the primes of `R` disjoint from the localized submonoid `M`. -/
@[stacks 00E3 "spectrum of a localization"]
def localizationHomeomorph (M : Submonoid R) :
    PrimeSpectrum (Localization M) ≃ₜ
      {p : PrimeSpectrum R // Disjoint (M : Set R) p.asIdeal} :=
  (localization_comap_isEmbedding (Localization M) M).toHomeomorph.trans
    (Homeomorph.setCongr (localization_comap_range (Localization M) M))

/-- The forward map of `localizationHomeomorph` is the prime comap along the
canonical localization map. -/
@[simp, stacks 00E3 "localization homeomorph forward map"]
theorem localizationHomeomorph_apply (M : Submonoid R)
    (p : PrimeSpectrum (Localization M)) :
    (localizationHomeomorph M p).1 =
      comap (algebraMap R (Localization M)) p := sorry
/- Proof strategy: unfold the composite homeomorphism and reduce the forward
map to `localization_comap_isEmbedding`. -/

/-- The inverse of `localizationHomeomorph` extends a prime disjoint from `M`
along the localization map. -/
@[stacks 00E3 "localization homeomorph inverse map"]
theorem localizationHomeomorph_symm_apply (M : Submonoid R)
    (p : {p : PrimeSpectrum R // Disjoint (M : Set R) p.asIdeal}) :
    (localizationHomeomorph M).symm p =
      ⟨p.1.asIdeal.map (algebraMap R (Localization M)),
        IsLocalization.isPrime_of_isPrime_disjoint M (Localization M) _ p.1.2 p.2⟩ := sorry
/- Proof strategy: use injectivity of localization comap and the standard
comap-map identity for an ideal disjoint from `M`. -/

/-- The inverse prime in `Localization M` has the expected extended ideal. -/
@[stacks 00E3 "localization inverse ideal"]
theorem localizationHomeomorph_symm_apply_asIdeal (M : Submonoid R)
    (p : {p : PrimeSpectrum R // Disjoint (M : Set R) p.asIdeal}) :
    ((localizationHomeomorph M).symm p).asIdeal =
      p.1.asIdeal.map (algebraMap R (Localization M)) := sorry
/- Proof strategy: project `localizationHomeomorph_symm_apply` to
`PrimeSpectrum.asIdeal`. -/

end PrimeSpectrum
