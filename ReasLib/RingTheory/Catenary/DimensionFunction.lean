/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
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

/-- The integer-valued Krull dimension of the quotient by a prime point.

The `unbotD`/`toNat` conversion is centralized here because
`IsDimensionFunction` is integer-valued, while `ringKrullDim` is
`WithBot ℕ∞`-valued. -/
@[stacks 0ECF "integer-valued prime-quotient Krull dimension"]
noncomputable def quotientKrullDim {A : Type u} [CommRing A] (p : PrimeSpectrum A) : ℤ :=
  (((ringKrullDim (A ⧸ p.asIdeal)).unbotD 0).toNat : ℤ)

/-- Unfolding the prime-quotient Krull dimension exposes its canonical model. -/
@[simp, stacks 0ECF "prime-quotient Krull dimension formula"]
theorem quotientKrullDim_apply {A : Type u} [CommRing A] (p : PrimeSpectrum A) :
    quotientKrullDim p = (((ringKrullDim (A ⧸ p.asIdeal)).unbotD 0).toNat : ℤ) := sorry

end PrimeSpectrum

/-- Lemma 10.105.10: a Noetherian local ring is catenary exactly when the function sending a
prime `p` to `dim (A ⧸ p)` is a dimension function on `Spec A`. -/
@[stacks 0ECF]
theorem isCatenaryRing_iff_primeQuotientKrullDimension_isDimensionFunction
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] :
    IsCatenaryRing A ↔
      IsDimensionFunction (PrimeSpectrum.quotientKrullDim (A := A)) := sorry
