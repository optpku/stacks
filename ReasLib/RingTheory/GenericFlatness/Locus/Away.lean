module

public import Mathlib.RingTheory.Localization.Away.AdjoinRoot
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.GenericFlatness.Localization.Away
public import ReasLib.RingTheory.GenericFlatness.Locus
public import ReasLib.RingTheory.Spectrum.Prime.Localization.Away

/-!
# The generic-flatness locus under principal localization

The main theorem follows Mathlib's localization-locus convention: the inverse
image of the original locus along `Spec(R_f) → Spec(R)` is the locus of the
localized algebra-module pair.
-/

@[expose] public section

universe u v w

namespace GenericFlatness

/- API design for 051X: inverse image along `Spec(R_f) → Spec(R)` is the canonical functorial
statement.  Its homeomorphism/image companion is retained as source-facing glue for consumers
working inside the basic open `D(f)` rather than the localized spectrum. -/

/-- Lemma 10.118.5 (1) (Tag 051X): pulling the generic-flatness good locus back along
`Spec(R_f) → Spec(R)` gives the good locus of the algebra-module pair localized away from `f`. -/
@[stacks 051X "(1), generic-flatness locus and principal localization"]
theorem goodLocus_comap_away
    {R : Type u} [CommRing R]
    {S : Type v} [CommRing S] [Algebra R S]
    {M : Type w} [AddCommGroup M] [Module S M]
    (f : R) :
    PrimeSpectrum.comap (algebraMap R (Localization.Away f)) ⁻¹' goodLocus R S M =
      goodLocusAway (R := R) (S := S) (M := M) f := sorry

/-- Lemma 10.118.5 (2) (Tag 051X): under the canonical homeomorphism
`Spec(R_f) ≃ D(f)`, the localized good locus is the restriction of the original good locus to
`D(f)`. -/
@[stacks 051X "(2), generic-flatness locus restricted to a basic open"]
theorem goodLocusAway_image_eq_restrict
    {R : Type u} [CommRing R]
    {S : Type v} [CommRing S] [Algebra R S]
    {M : Type w} [AddCommGroup M] [Module S M]
    (f : R) :
    Set.image (PrimeSpectrum.localizationAwayHomeomorph f)
      (goodLocusAway (R := R) (S := S) (M := M) f) =
      ((↑) : PrimeSpectrum.basicOpen f → PrimeSpectrum R) ⁻¹' goodLocus R S M := sorry

end GenericFlatness
