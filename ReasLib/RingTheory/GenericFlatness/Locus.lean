module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.GenericFlatness.Localization

/-!
# The generic-flatness locus

The good locus is the union of principal opens on which the generic-flatness
localization condition holds.

@stack 051T
-/

@[expose] public section

open PrimeSpectrum

universe u v w

namespace GenericFlatness

/-- The good locus for an algebra and module: the union of principal opens where the generic
flatness localization condition holds. -/
@[stacks 051T "generic-flatness good locus"]
def goodLocus
    (R : Type u) [CommRing R]
    (S : Type v) [CommRing S] [Algebra R S]
    (M : Type w) [AddCommGroup M] [Module S M] : Set (PrimeSpectrum R) :=
  ⋃ f : {f : R // LocalizationCondition R S M f},
    (basicOpen f.1 : Set (PrimeSpectrum R))

/-- The good locus is the displayed union of the corresponding principal opens. -/
theorem goodLocus_eq_iUnion
    {R : Type u} [CommRing R]
    {S : Type v} [CommRing S] [Algebra R S]
    {M : Type w} [AddCommGroup M] [Module S M] :
    goodLocus R S M =
      ⋃ f : {f : R // LocalizationCondition R S M f},
        (basicOpen f.1 : Set (PrimeSpectrum R)) := sorry

/-- Membership in the generic-flatness good locus is witnessed by one localization parameter
that does not belong to the given prime. -/
theorem mem_goodLocus_iff
    {R : Type u} [CommRing R]
    {S : Type v} [CommRing S] [Algebra R S]
    {M : Type w} [AddCommGroup M] [Module S M]
    (p : PrimeSpectrum R) :
    p ∈ goodLocus R S M ↔ ∃ f : R, LocalizationCondition R S M f ∧ f ∉ p.asIdeal := sorry

/-- The good locus of the algebra-module pair obtained by localizing away from `f`.  The
relative `R_f`-algebra structure on the localized target is fixed locally, avoiding an action
diamond with native localization actions. -/
noncomputable abbrev goodLocusAway
    {R : Type u} [CommRing R]
    {S : Type v} [CommRing S] [Algebra R S]
    {M : Type w} [AddCommGroup M] [Module S M]
(f : R) : Set (PrimeSpectrum (Localization.Away f)) :=
  -- Local declaration justification (instance diamond): the relative localized target action is
  -- selected by the named support API rather than installed as a competing global instance.
  letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
    Localization.Away.Relative.algebraMapAlgebra f
  goodLocus (Localization.Away f)
    (Localization.Away (algebraMap R S f))
    (LocalizedModule.Away (algebraMap R S f) M)

end GenericFlatness
