/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.LimitTopology
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.Polynomial.Quotient

@[expose] public section

noncomputable section

universe u v

/-- The restricted power series ring is realized as the adic completion of the polynomial
ring along the extended coefficient ideal. -/
abbrev IAdicRestrictedPowerSeries {A : Type u} [CommRing A] (σ : Type v) (I : Ideal A) : Type (max u v) :=
  AdicCompletion (I.map (algebraMap A (MvPolynomial σ A))) (MvPolynomial σ A)

namespace IAdicRestrictedPowerSeries

variable {A : Type u} [CommRing A] (σ : Type v) (I : Ideal A)

/-- The coefficient ideal extended to the adic completion of the polynomial ring. -/
def extendedIdeal : Ideal (IAdicRestrictedPowerSeries σ I) :=
  Ideal.map (algebraMap (MvPolynomial σ A) (IAdicRestrictedPowerSeries σ I))
    (I.map (algebraMap A (MvPolynomial σ A)))

/-- The canonical algebra map to polynomials with coefficients reduced modulo `I ^ n`. -/
def stageHom (n : ℕ) : IAdicRestrictedPowerSeries σ I →ₐ[A] MvPolynomial σ (A ⧸ I ^ n) :=
  (MvPolynomial.quotientEquivQuotientMvPolynomial (I ^ n)).symm.toAlgHom.comp
    ((Ideal.quotientEquivAlgOfEq A
        (Ideal.map_pow (algebraMap A (MvPolynomial σ A)) I n).symm).toAlgHom.comp
      ((AdicCompletion.evalₐ (I.map (algebraMap A (MvPolynomial σ A))) n).restrictScalars A))

/-- A polynomial maps to its coefficientwise reduction modulo `I ^ n`. -/
theorem stageHom_map (n : ℕ) (p : MvPolynomial σ A) :
    stageHom σ I n (algebraMap (MvPolynomial σ A) (IAdicRestrictedPowerSeries σ I) p) =
      MvPolynomial.map (Ideal.Quotient.mk (I ^ n)) p := sorry

/-- Constants map to constant polynomials with coefficients reduced modulo `I ^ n`. -/
theorem stageHom_C (n : ℕ) (coefficient : A) :
    stageHom σ I n (algebraMap A (IAdicRestrictedPowerSeries σ I) coefficient) =
      MvPolynomial.C (Ideal.Quotient.mk (I ^ n) coefficient) := sorry

/-- Indeterminates remain indeterminates in every polynomial stage. -/
theorem stageHom_X (n : ℕ) (index : σ) :
    stageHom σ I n
        (algebraMap (MvPolynomial σ A) (IAdicRestrictedPowerSeries σ I) (MvPolynomial.X index)) =
      MvPolynomial.X index := sorry

/-- Stage maps commute with coefficient reduction from stage `n` to stage `m ≤ n`. -/
theorem stageHom_comp {m n : ℕ} (hmn : m ≤ n) (series : IAdicRestrictedPowerSeries σ I) :
    MvPolynomial.map (Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn))
        (stageHom σ I n series) = stageHom σ I m series := sorry

/-- A family of polynomial stages is compatible if all coefficient-reduction maps agree. -/
def CompatibleStages (family : (n : ℕ) → MvPolynomial σ (A ⧸ I ^ n)) : Prop :=
  ∀ ⦃m n : ℕ⦄ (hmn : m ≤ n),
    MvPolynomial.map (Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn)) (family n) = family m

/-- The inverse-limit topology on the adic completion of the polynomial ring. -/
@[implicit_reducible]
def limitTopology : TopologicalSpace (IAdicRestrictedPowerSeries σ I) :=
  (AdicCompletion.limitUniformSpace (I.map (algebraMap A (MvPolynomial σ A)))).toTopologicalSpace

/-- Over an adically complete coefficient ring, every compatible polynomial-stage family
has a unique lift through the canonical stage algebra maps. -/
theorem compatibleStages_liftUnique [IsAdicComplete I A]
    (family : (n : ℕ) → MvPolynomial σ (A ⧸ I ^ n))
    (h_compatible : CompatibleStages σ I family) :
    ∃! series : IAdicRestrictedPowerSeries σ I, ∀ n, stageHom σ I n series = family n := sorry

/-- For a finitely generated coefficient ideal, the inverse-limit topology is the adic
topology of its extension, specializing the generic completion topology comparison. -/
theorem limitTopology_eq_adic [IsAdicComplete I A] (hI : I.FG) :
    limitTopology σ I = (extendedIdeal σ I).adicTopology := sorry

end IAdicRestrictedPowerSeries
