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
public import ReasLib.RingTheory.Invariant.Quotient
public import ReasLib.RingTheory.RingHom.ShiftPower.Spectrum

@[expose] public section

/-!
# Spectral consequences for fixed points of quotients

The quotient construction lives in `Invariant.Quotient`; this leaf contains only the finite-group
consequences.  Splitting the layers keeps the algebraic construction usable without importing
prime-spectrum or residue-field infrastructure.
@stack 09EG
-/

open PrimeSpectrum

universe u v

namespace Ideal.Quotient.FixedPoints

variable {R : Type u} {G : Type v} [CommRing R] [Group G] [MulSemiringAction G R]
variable [Finite G]
variable (I : Ideal R) (hI : I.IsStable G)

/-- The fixed-point quotient map is shift-power generated for a finite group. -/
@[stacks 09EG "fixed-point quotient shift-power generation"]
theorem map_isGenerated :
    RingHom.ShiftPower.IsGenerated (Ideal.Quotient.fixedPointsMap I hI) := sorry
-- Proof strategy: give `fixedPointsMap I hI` its canonical algebra structure and prove top
-- generation elementwise.  For a fixed quotient class `b`, apply
-- `MulSemiringActionHom.exists_monic_map_eq_orbit` to the surjective equivariant map
-- `Ideal.Quotient.mkHom I hI`; map the resulting polynomial through the source quotient and use
-- `Ideal.Quotient.fixedPointsMap_comp_mk` plus `Polynomial.map_map` to obtain the required
-- shift-power witness.  Finish with `Algebra.subset_adjoin` and `Nat.card_pos`.

/-- The fixed-point quotient map is integral. -/
@[stacks 09EG "fixed-point quotient integrality"]
theorem map_isIntegral : (Ideal.Quotient.fixedPointsMap I hI).IsIntegral := sorry
-- Proof strategy: apply `RingHom.ShiftPower.isIntegral` to `map_isGenerated I hI`.

/-- The induced map on prime spectra is a homeomorphism. -/
@[stacks 09EG "fixed-point quotient spectrum homeomorphism"]
theorem map_isHomeomorph :
    IsHomeomorph (PrimeSpectrum.comap (Ideal.Quotient.fixedPointsMap I hI)) := sorry
-- Proof strategy: apply `RingHom.ShiftPower.Spectrum.isHomeomorph_comap` with
-- `map_isGenerated I hI`; rewrite the kernel using `Ideal.Quotient.FixedPoints.map_ker`, after
-- which local nilpotence is the order-theoretic fact `⊥ ≤ Ideal.nilradical _`.

/-- The fixed-point quotient map induces purely inseparable residue-field extensions. -/
@[stacks 09EG "fixed-point quotient residue fields"]
theorem map_residueField :
    RingHom.ResidueField.MapsPurelyInseparable
      (Ideal.Quotient.fixedPointsMap I hI) := sorry
-- Proof strategy: apply
-- `RingHom.ShiftPower.Spectrum.residueField_isPurelyInseparable` to `map_isGenerated I hI`.

/-- The finite-group fixed-point quotient map satisfies all three standard spectral conclusions. -/
@[stacks 09EG "fixed-point quotient spectral package"]
theorem map_spec :
    (Ideal.Quotient.fixedPointsMap I hI).IsIntegral ∧
      IsHomeomorph (PrimeSpectrum.comap (Ideal.Quotient.fixedPointsMap I hI)) ∧
      RingHom.ResidueField.MapsPurelyInseparable
        (Ideal.Quotient.fixedPointsMap I hI) := sorry
-- Proof strategy: assemble `map_isIntegral I hI`, `map_isHomeomorph I hI`, and
-- `map_residueField I hI` into the stated nested conjunction.

end Ideal.Quotient.FixedPoints
