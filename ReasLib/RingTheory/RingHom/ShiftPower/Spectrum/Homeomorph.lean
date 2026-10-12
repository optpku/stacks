/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.LocallyNilpotent
public import ReasLib.RingTheory.RingHom.ShiftPower.PowerSurjective
public import ReasLib.RingTheory.RingHom.Spectrum.PowerRange
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Spectral homeomorphisms from shift-power generation

This leaf specializes the bundled positive-power-surjective spectral API to
shift-power generation.  It is separate from the larger spectrum aggregation
file so its proof obligation can be scheduled independently.
@stack 0BRH
-/

@[expose] public section

open PrimeSpectrum

universe u v

namespace RingHom.ShiftPower.Spectrum

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- A locally nilpotent kernel and shift-power generation induce a homeomorphism on spectra.
This is the shift-power specialization of `RingHom.IsPowerSurjective.isHomeomorph_comap`. -/
@[stacks 09EF "shift-power spectral homeomorphism",
  stacks 0BRH "spectral homeomorphism for the shift-power invariant criterion"]
theorem isHomeomorph_comap
    (f : R →+* S) (hker : (RingHom.ker f).IsLocallyNilpotent)
    (hgen : IsGenerated f) :
    IsHomeomorph (comap f) := sorry

end RingHom.ShiftPower.Spectrum
