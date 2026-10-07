module

public import ReasLib.RingTheory.Ideal.LocallyNilpotent
public import ReasLib.RingTheory.RingHom.Fiber.PurelyInseparable
public import ReasLib.RingTheory.RingHom.PowerGeneration.BaseChange
public import ReasLib.RingTheory.RingHom.Spectrum.BaseChange
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Spectral consequences of prime-power generation

This leaf packages the consequences of prime-power and scalar-image generation
which do not depend on the presentation of a particular chapter.

@stack 0BRA
-/

@[expose] public section

open PrimeSpectrum

universe u v w

namespace RingHom

namespace PowerGeneration

namespace Spectrum

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- Lemma 10.46.7 (Tag 0BRA): at every target prime, prime-power/scalar-image generation gives
the source-level residue-field alternative.  The purely inseparable branch is owned by the
canonical induced residue-field map rather than by a locally installed algebra instance. -/
@[stacks 0BRA "residue-field alternative"]
theorem residueField_criterion
    {p : ℕ} [Fact p.Prime] (f : R →+* S) (hgen : IsGenerated f p)
    (q : PrimeSpectrum S) :
    Function.Surjective
        (Ideal.ResidueField.map (comap f q).asIdeal q.asIdeal f rfl) ∨
      ringChar (comap f q).asIdeal.ResidueField = p ∧
        ResidueField.IsPurelyInseparableAt f q := sorry

/-- Prime-power and scalar-image generation induces purely inseparable extensions on residue
fields. -/
@[stacks 0BRA]
theorem residueField_isPurelyInseparable
    {p : ℕ} [Fact p.Prime] (f : R →+* S) (hgen : IsGenerated f p) :
    ResidueField.MapsPurelyInseparable f := sorry

/-- Prime-power and scalar-image generation with a locally nilpotent kernel induces a
homeomorphism on prime spectra. -/
@[stacks 0BRA]
theorem isHomeomorph_comap
    {p : ℕ} [Fact p.Prime] (f : R →+* S)
    (hgen : IsGenerated f p) (hker : (RingHom.ker f).IsLocallyNilpotent) :
    IsHomeomorph (comap f) := sorry

namespace BaseChange

/-- A locally nilpotent kernel remains locally nilpotent after base change under the
prime-power generation hypothesis. -/
@[stacks 0BRA]
theorem ker_isLocallyNilpotent
    {p : ℕ} [Fact p.Prime] {R' : Type w} [CommRing R']
    (f : R →+* S) (g : R →+* R')
    (hgen : IsGenerated f p) (hker : (RingHom.ker f).IsLocallyNilpotent) :
    (RingHom.ker (f.baseChange g)).IsLocallyNilpotent := sorry

/-- The spectral homeomorphism persists after base change under the prime-power generation and
locally nilpotent-kernel hypotheses. -/
@[stacks 0BRA]
theorem isHomeomorph_comap
    {p : ℕ} [Fact p.Prime] {R' : Type w} [CommRing R']
    (f : R →+* S) (g : R →+* R')
    (hgen : IsGenerated f p) (hker : (RingHom.ker f).IsLocallyNilpotent) :
    IsHomeomorph (comap (f.baseChange g)) := sorry

/-- Purely inseparable residue-field extensions persist after base change under the prime-power
generation hypothesis. -/
@[stacks 0BRA]
theorem residueField_isPurelyInseparable
    {p : ℕ} [Fact p.Prime] {R' : Type w} [CommRing R']
    (f : R →+* S) (g : R →+* R') (hgen : IsGenerated f p) :
    ResidueField.MapsPurelyInseparable (f.baseChange g) := sorry

end BaseChange

end Spectrum

end PowerGeneration

end RingHom
