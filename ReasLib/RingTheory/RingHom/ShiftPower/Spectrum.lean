/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.RingHom.Fiber.PurelyInseparable
public import ReasLib.RingTheory.RingHom.ShiftPower.BaseChange
public import ReasLib.RingTheory.RingHom.ShiftPower.Spectrum.Homeomorph
public import ReasLib.RingTheory.RingHom.ShiftPower.PowerSurjective
public import ReasLib.RingTheory.Ideal.LocallyNilpotent
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Spectral consequences of shift-power generation

This leaf owns the reusable spectral and residue-field consequences of the
shift-power generation predicate. The chapter file can therefore retain only
source-facing packaging and recall blocks.

@stack 09EF
-/

@[expose] public section

open PrimeSpectrum

universe u v w

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

namespace ShiftPower

namespace Spectrum

/-- A field-source shift-power generated map has a positive source-image power for every target
element. -/
lemma Field.exists_pow_mem
    {K : Type*} {A : Type*} [Field K] [CommRing A] (φ : K →+* A)
    (hgen : IsGenerated φ) :
    ∀ x : A, ∃ n : ℕ, 0 < n ∧ x ^ n ∈ φ.range := sorry

/-- Shift-power generation makes the map on prime spectra injective. -/
@[stacks 09EF]
theorem comap_injective
    (f : R →+* S) (hgen : IsGenerated f) :
    Function.Injective (comap f) := sorry

/-- With locally nilpotent kernel, shift-power generation makes the map on prime spectra
bijective. -/
@[stacks 09EF]
theorem comap_bijective
    (f : R →+* S) (hker : (RingHom.ker f).IsLocallyNilpotent)
    (hgen : IsGenerated f) :
    Function.Bijective (comap f) := sorry

/-- Shift-power generation implies purely inseparable maps on all residue fields. -/
@[stacks 09EF, stacks 0BRH "purely inseparable residue fields"]
theorem residueField_isPurelyInseparable
    (f : R →+* S) (hgen : IsGenerated f) :
    ResidueField.MapsPurelyInseparable f := sorry

namespace BaseChange

/-- The locally nilpotent kernel condition is preserved under tensor-product base change along an
arbitrary ring homomorphism. -/
@[stacks 09EF]
theorem ker_isLocallyNilpotent
    {R' : Type w} [CommRing R']
    (f : R →+* S) (g : R →+* R')
    (hker : (RingHom.ker f).IsLocallyNilpotent)
    (hgen : IsGenerated f) :
    (RingHom.ker (f.baseChange g)).IsLocallyNilpotent := sorry

/-- Ambient-algebra specialization of the base-change kernel theorem. -/
theorem ker_isLocallyNilpotent_algebraMap
    {R' : Type w} [CommRing R'] [Algebra R R']
    (f : R →+* S) (hker : (RingHom.ker f).IsLocallyNilpotent)
    (hgen : IsGenerated f) :
    (RingHom.ker (f.baseChangeAlgebraMap (R' := R'))).IsLocallyNilpotent := sorry

/-- The spectral homeomorphism persists after tensor-product base change along an arbitrary ring
homomorphism. -/
@[stacks 09EF]
theorem isHomeomorph_comap
    {R' : Type w} [CommRing R']
    (f : R →+* S) (g : R →+* R')
    (hker : (RingHom.ker f).IsLocallyNilpotent)
    (hgen : IsGenerated f) :
    IsHomeomorph (comap (f.baseChange g)) := sorry

/-- Ambient-algebra specialization of the base-change spectral homeomorphism theorem. -/
theorem isHomeomorph_comap_algebraMap
    {R' : Type w} [CommRing R'] [Algebra R R']
    (f : R →+* S) (hker : (RingHom.ker f).IsLocallyNilpotent)
    (hgen : IsGenerated f) :
    IsHomeomorph (comap (f.baseChangeAlgebraMap (R' := R'))) := sorry

/-- Purely inseparable residue-field maps persist after tensor-product base change along an
arbitrary ring homomorphism. -/
@[stacks 09EF]
theorem residueField_isPurelyInseparable
    {R' : Type w} [CommRing R']
    (f : R →+* S) (g : R →+* R') (hgen : IsGenerated f) :
    ResidueField.MapsPurelyInseparable (f.baseChange g) := sorry

/-- Ambient-algebra specialization of the base-change residue-field theorem. -/
theorem residueField_isPurelyInseparable_algebraMap
    {R' : Type w} [CommRing R'] [Algebra R R']
    (f : R →+* S) (hgen : IsGenerated f) :
    ResidueField.MapsPurelyInseparable (f.baseChangeAlgebraMap (R' := R')) := sorry

end BaseChange

end Spectrum

end ShiftPower

end RingHom
