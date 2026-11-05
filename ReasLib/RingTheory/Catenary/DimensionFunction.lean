/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Catenary.Basic
public import ReasLib.Topology.Specialization.Dimension.Catenary

@[expose] public section

/-!
# Catenarity and Dimension Functions

The local ring criterion identifies the source ring-theoretic catenarity
condition with the existing topological dimension-function owner.

@stack 0ECF
-/

universe u

namespace PrimeSpectrum

/-- A prime quotient of a finite-dimensional ring is finite-dimensional. -/
instance finiteRingKrullDim_quotient {A : Type u} [CommRing A]
    [FiniteRingKrullDim A] (p : PrimeSpectrum A) : FiniteRingKrullDim (A ⧸ p.asIdeal) := by
  apply finiteRingKrullDim_iff_ne_bot_and_top.mpr
  constructor
  · exact ne_of_gt (lt_of_lt_of_le (WithBot.bot_lt_coe (0 : ℕ∞))
      ringKrullDim_nonneg_of_nontrivial)
  · exact ne_of_lt ((ringKrullDim_quotient_le p.asIdeal).trans_lt ringKrullDim_lt_top)

/-- The integer-valued Krull dimension of a finite-dimensional prime quotient.

Only this quotient is required to have finite dimension. For arbitrary prime quotients,
including those of infinite dimension, use `ringKrullDim (A ⧸ p.asIdeal)` directly.
The finiteness assumption makes the `unbotD`/`toNat` conversion lossless, as recorded by
`quotientKrullDim_natCast`. -/
@[stacks 0ECF "integer-valued finite prime-quotient Krull dimension"]
noncomputable def quotientKrullDim {A : Type u} [CommRing A] (p : PrimeSpectrum A)
    [FiniteRingKrullDim (A ⧸ p.asIdeal)] : ℤ :=
  (((ringKrullDim (A ⧸ p.asIdeal)).unbotD 0).toNat : ℤ)

/-- Unfolding the finite prime-quotient Krull dimension exposes its canonical model. -/
@[simp, stacks 0ECF "finite prime-quotient Krull dimension formula"]
theorem quotientKrullDim_apply {A : Type u} [CommRing A] (p : PrimeSpectrum A)
    [FiniteRingKrullDim (A ⧸ p.asIdeal)] :
    quotientKrullDim p = (((ringKrullDim (A ⧸ p.asIdeal)).unbotD 0).toNat : ℤ) := rfl

/-- Integer extraction preserves the extended Krull dimension of a finite prime quotient. -/
theorem quotientKrullDim_natCast {A : Type u} [CommRing A] (p : PrimeSpectrum A)
    [FiniteRingKrullDim (A ⧸ p.asIdeal)] :
    ((quotientKrullDim p).toNat : WithBot ℕ∞) = ringKrullDim (A ⧸ p.asIdeal) := by
  simp [quotientKrullDim, ringKrullDim, Order.krullDim_eq_length_of_finiteDimensionalOrder]

end PrimeSpectrum

/-- Lemma 10.105.10: a Noetherian local ring is catenary exactly when the function sending a
prime `p` to `dim (A ⧸ p)` is a dimension function on `Spec A`. -/
@[stacks 0ECF]
theorem isCatenaryRing_iff_primeQuotientKrullDimension_isDimensionFunction
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] :
    IsCatenaryRing A ↔
      IsDimensionFunction (fun p : PrimeSpectrum A ↦ PrimeSpectrum.quotientKrullDim p) := sorry
