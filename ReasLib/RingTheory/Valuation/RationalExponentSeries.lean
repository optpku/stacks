/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.NNRat.Order
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Finite
public import ReasLib.RingTheory.Topology.WeaklyAdmissible
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.HahnSeries.Multiplication
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import ReasLib.RingTheory.Valuation.RankOneAdic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReasLib.RingTheory.Completion.LocalRing
public import ReasLib.RingTheory.Topology.Adic.Hom

/-!
# Nonnegative rational-exponent series

The ring of series `∑ a_α t^α` with `α ∈ ℚ≥0` and only finitely many
nonzero coefficients of exponent `≤ n` for each `n : ℕ`, realized as a
subring of `HahnSeries ℚ≥0 κ`.
-/

@[expose] public section

noncomputable section

universe u

open HahnSeries IsLocalRing

/-- The ring of nonnegative rational-exponent series with coefficients in `κ`
whose support is finite on each initial interval `Set.Iic (n : ℚ≥0)`. -/
def RationalExponentSeries (κ : Type u) [CommRing κ] : Subring (HahnSeries ℚ≥0 κ) where
  carrier := {f | ∀ n : ℕ, (f.support ∩ Set.Iic (n : ℚ≥0)).Finite}
  add_mem' := by
    intro left right leftFinite rightFinite cutoff
    apply ((leftFinite cutoff).union (rightFinite cutoff)).subset
    intro exponent membership
    rcases HahnSeries.support_add_subset left right membership.1 with inLeft | inRight
    · exact Or.inl ⟨inLeft, membership.2⟩
    · exact Or.inr ⟨inRight, membership.2⟩
  zero_mem' := by
    intro cutoff
    simp
  mul_mem' := by
    intro left right leftFinite rightFinite cutoff
    apply ((leftFinite cutoff).image2 (· + ·) (rightFinite cutoff)).subset
    intro exponent membership
    rcases HahnSeries.support_mul_subset membership.1 with
      ⟨leftExponent, inLeft, rightExponent, inRight, rfl⟩
    exact Set.mem_image2.mpr ⟨leftExponent,
      ⟨inLeft, le_trans
        (le_add_of_nonneg_right (zero_le : (0 : ℚ≥0) ≤ rightExponent)) membership.2⟩,
      rightExponent,
      ⟨inRight, le_trans
        (le_add_of_nonneg_left (zero_le : (0 : ℚ≥0) ≤ leftExponent)) membership.2⟩,
      rfl⟩
  one_mem' := by
    intro cutoff
    exact (Set.finite_singleton (0 : ℚ≥0)).subset fun exponent membership =>
      HahnSeries.support_single_subset membership.1
  neg_mem' := by
    intro series seriesFinite cutoff
    exact (seriesFinite cutoff).subset fun exponent membership =>
      ⟨HahnSeries.support_neg_subset series membership.1, membership.2⟩

namespace RationalExponentSeries

/-- Membership in `RationalExponentSeries κ` is the bounded-support condition. -/
theorem mem_iff {κ : Type u} [CommRing κ] {f : HahnSeries ℚ≥0 κ} :
    f ∈ RationalExponentSeries κ ↔
      ∀ n : ℕ, (f.support ∩ Set.Iic (n : ℚ≥0)).Finite :=
  sorry

/-- The monomial of exponent one has finite support in every bounded interval. -/
theorem t_mem (κ : Type u) [CommRing κ] :
    HahnSeries.single (1 : ℚ≥0) 1 ∈ RationalExponentSeries κ := by
  intro cutoff
  exact (Set.finite_singleton (1 : ℚ≥0)).subset fun exponent membership =>
    HahnSeries.support_single_subset membership.1

/-- The monomial `t` of exponent `1`. -/
def t (κ : Type u) [CommRing κ] : RationalExponentSeries κ :=
  ⟨HahnSeries.single (1 : ℚ≥0) 1, t_mem κ⟩

/-- The monomial `t` is nonzero when the coefficient ring is a field. -/
theorem t_ne_zero (κ : Type u) [Field κ] : t κ ≠ 0 :=
  sorry

/-- The `t`-adic topology on the rational-exponent series ring. -/
instance instTopologicalSpace (κ : Type u) [CommRing κ] :
    TopologicalSpace (RationalExponentSeries κ) :=
  (Ideal.span {t κ}).adicTopology

/-- The `t`-adic topology is a ring topology. -/
instance instIsTopologicalRing (κ : Type u) [CommRing κ] :
    IsTopologicalRing (RationalExponentSeries κ) :=
  sorry

/-- The ambient topology on the series ring is the `t`-adic topology. -/
theorem isAdic_span_t (κ : Type u) [CommRing κ] :
    IsAdic (Ideal.span {t κ}) :=
  sorry

/-- The `t`-adic topology on the rational-exponent series ring is pre-adic. -/
instance instIsPreadicRing (κ : Type u) [CommRing κ] :
    TopologicalRing.IsPreadicRing (RationalExponentSeries κ) where
  exists_ideal_isAdic := ⟨Ideal.span {t κ}, isAdic_span_t κ⟩

/-- The rational-exponent series ring over a field is a domain. -/
instance instIsDomain (κ : Type u) [Field κ] : IsDomain (RationalExponentSeries κ) :=
  sorry

/-- The rational-exponent series ring over a field is a valuation ring. -/
instance instValuationRing (κ : Type u) [Field κ] : ValuationRing (RationalExponentSeries κ) :=
  sorry

/-- The valuative relation induced by the fraction-field valuation restricted to the series ring. -/
@[reducible]
def valuativeRel (κ : Type u) [Field κ] : ValuativeRel (RationalExponentSeries κ) :=
  ValuativeRel.ofValuation (ValuationRing.Adic.valuationRingComap (RationalExponentSeries κ))

/-- The series ring carries its canonical restricted-valuation relation. -/
instance instValuativeRel (κ : Type u) [Field κ] : ValuativeRel (RationalExponentSeries κ) :=
  valuativeRel κ

/-- Comparison in the series ring is comparison of its canonical restricted valuation. -/
theorem vle_iff (κ : Type u) [Field κ] (left right : RationalExponentSeries κ) :
    left ≤ᵥ right ↔
      ValuationRing.Adic.valuationRingComap (RationalExponentSeries κ) left ≤
        ValuationRing.Adic.valuationRingComap (RationalExponentSeries κ) right :=
  Iff.rfl

/-- The fraction-field valuation is compatible with the canonical series-ring relation. -/
instance instCompatible_valuationRing_comap (κ : Type u) [Field κ] :
    Valuation.Compatible (ValuationRing.Adic.valuationRingComap (RationalExponentSeries κ)) :=
  sorry

/-- The canonical valuative relation on the rational-exponent series ring has rank at most one. -/
instance instIsRankLeOne (κ : Type u) [Field κ] :
    ValuativeRel.IsRankLeOne (RationalExponentSeries κ) :=
  sorry

/-- The rational-exponent series ring is `t`-adically complete. -/
instance instIsAdicComplete_span_t (κ : Type u) [Field κ] :
    IsAdicComplete (Ideal.span {t κ}) (RationalExponentSeries κ) :=
  sorry

/-- The monomial `t` lies in the maximal ideal. -/
theorem t_mem_maximalIdeal (κ : Type u) [Field κ] :
    t κ ∈ maximalIdeal (RationalExponentSeries κ) :=
  sorry

/-- The rational-exponent series ring is weakly admissible in its `t`-adic topology. -/
instance instIsWeaklyAdmissibleRing (κ : Type u) [Field κ] :
    TopologicalRing.IsWeaklyAdmissibleRing (RationalExponentSeries κ) :=
  sorry

/-- The monomial `t` is nonzero and belongs to the non-finitely-generated maximal
ideal of the rational-exponent series ring over a field. -/
theorem «example» (κ : Type u) [Field κ] :
    t κ ∈ maximalIdeal (RationalExponentSeries κ) ∧
      t κ ≠ 0 ∧ ¬ (maximalIdeal (RationalExponentSeries κ)).FG :=
  sorry

/-- There is no adic ring map from the rational-exponent series ring to a
complete discrete valuation ring equipped with its maximal-adic topology. -/
theorem not_isAdicHom_completeDVR {κ R : Type u} [Field κ] [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [IsCompleteLocalRing R] [TopologicalSpace R]
    [TopologicalRing.IsPreadicRing R] (hR : IsAdic (maximalIdeal R))
    (φ : RationalExponentSeries κ →+* R) : ¬ φ.IsAdicHom :=
  sorry

/-- The radical of the ideal generated by `t` is the maximal ideal of the
rational-exponent series ring over a field. -/
theorem radical_span_t_eq_maximalIdeal (κ : Type u) [Field κ] :
    (Ideal.span {t κ}).radical = maximalIdeal (RationalExponentSeries κ) :=
  sorry

end RationalExponentSeries
