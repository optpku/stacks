/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Ideal.LocallyNilpotent
public import ReasLib.RingTheory.Invariant.FixedPoints.IdealQuotient
public import ReasLib.RingTheory.RingHom.ShiftPower.Spectrum

@[expose] public section

/-!
# Spectral consequences for quotients of fixed-point subrings

The algebraic quotient map and its polynomial witnesses are owned by
`FixedPoints.Quotient`. This leaf records the kernel, spectrum, and residue-field consequences
without importing any chapter-facing module.

@stack 0H35
-/

open PrimeSpectrum

universe u v

namespace FixedPoints.Quotient

variable {R : Type u} {G : Type v} [CommRing R] [Group G] [MulSemiringAction G R]
variable [Finite G]

/-- The kernel of the fixed-subring quotient map is locally nilpotent. -/
@[stacks 0H35 "locally nilpotent kernel of the fixed-subring quotient map"]
theorem ker_isLocallyNilpotent (J : Ideal (FixedPoints.subring R G)) :
    (RingHom.ker (map J)).IsLocallyNilpotent := sorry
-- Proof strategy: use `Ideal.isLocallyNilpotent_iff`.  For `a` in the kernel, apply `kernel_pow J`
-- to the bundled element `⟨a, ha⟩`, evaluate the polynomial identity at `0`, and use
-- `Nat.card_pos` to conclude that `-a`, hence `a`, is nilpotent.

/-- The fixed-subring quotient map induces a homeomorphism on prime spectra. -/
@[stacks 0H35 "spectrum homeomorphism for the fixed-subring quotient map"]
theorem isHomeomorph (J : Ideal (FixedPoints.subring R G)) :
    IsHomeomorph (PrimeSpectrum.comap (map J)) := sorry
-- Proof strategy: apply `RingHom.ShiftPower.Spectrum.isHomeomorph_comap` to
-- `ker_isLocallyNilpotent J` and `isGenerated J`.

/-- The fixed-subring quotient map induces purely inseparable residue-field extensions. -/
@[stacks 0H35 "purely inseparable residue fields for the fixed-subring quotient map"]
theorem residueField_isPurelyInseparable (J : Ideal (FixedPoints.subring R G)) :
    RingHom.ResidueField.MapsPurelyInseparable (map J) := sorry
-- Proof strategy: apply
-- `RingHom.ShiftPower.Spectrum.residueField_isPurelyInseparable` to `isGenerated J`.

end FixedPoints.Quotient
