module

public import ReasLib.FieldTheory.PrimeField.PowerCriterion
public import ReasLib.RingTheory.RingHom.Spectrum.PowerRange
public import Mathlib.RingTheory.RingHom.PurelyInseparable
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Residue fields of positive-power maps

This leaf owns the field-theoretic residue-field alternative for a positive-power-surjective
ring homomorphism.  The ring-theoretic spectrum layer only owns the map predicate and its
purely spectral consequences; the prime-field branch is kept here with the field criterion.

@stack 0BR8
-/

@[expose] public section

universe u v

namespace RingHom

namespace PowerRange

/-- Lemma 10.46.3 (Tag 0BR8): at every target prime, a positive-power-surjective ring
homomorphism induces a residue-field map that is purely inseparable or whose target is algebraic
over a prime field. -/
@[stacks 0BR8]
theorem residueField_criterion
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (hpow : f.IsPowerSurjective) (q : PrimeSpectrum S) :
    (Ideal.ResidueField.map (PrimeSpectrum.comap f q).asIdeal q.asIdeal f rfl).IsPurelyInseparable ∨
      FieldExtension.IsPrimeAlgebraic q.asIdeal.ResidueField := sorry

end PowerRange

end RingHom
