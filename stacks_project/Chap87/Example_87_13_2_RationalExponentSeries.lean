module

public import Mathlib.Data.NNRat.Order
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.HahnSeries.Multiplication
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology

/-!
# Nonnegative rational-exponent series

The source ring of series `∑ a_α t^α` with `α ∈ ℚ≥0` and only finitely many
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
  add_mem' := sorry
  zero_mem' := sorry
  mul_mem' := sorry
  one_mem' := sorry
  neg_mem' := sorry

namespace RationalExponentSeries

/-- Membership in `RationalExponentSeries κ` is the source support condition. -/
theorem mem_iff {κ : Type u} [CommRing κ] {f : HahnSeries ℚ≥0 κ} :
    f ∈ RationalExponentSeries κ ↔
      ∀ n : ℕ, (f.support ∩ Set.Iic (n : ℚ≥0)).Finite :=
  sorry

/-- The monomial `t` of exponent `1`. -/
def t (κ : Type u) [CommRing κ] : RationalExponentSeries κ :=
  ⟨HahnSeries.single (1 : ℚ≥0) 1, sorry⟩

/-- The monomial `t` lies in the rational-exponent series ring. -/
theorem t_mem (κ : Type u) [CommRing κ] :
    HahnSeries.single (1 : ℚ≥0) 1 ∈ RationalExponentSeries κ :=
  sorry

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

/-- The rational-exponent series ring over a field is a domain. -/
instance instIsDomain (κ : Type u) [Field κ] : IsDomain (RationalExponentSeries κ) :=
  sorry

/-- The rational-exponent series ring over a field is a valuation ring. -/
instance instValuationRing (κ : Type u) [Field κ] : ValuationRing (RationalExponentSeries κ) :=
  sorry

/-- The valuative relation on the series ring induced by the valuation-ring
valuation on its fraction field. -/
instance instValuativeRel (κ : Type u) [Field κ] :
    ValuativeRel (RationalExponentSeries κ) :=
  ValuativeRel.ofValuation <|
    (ValuationRing.valuation (RationalExponentSeries κ)
        (FractionRing (RationalExponentSeries κ))).comap <|
      algebraMap (RationalExponentSeries κ) (FractionRing (RationalExponentSeries κ))

/-- The canonical valuation-ring valuation of the series ring is compatible
with its valuative relation. -/
instance instCompatible_valuationRing_comap (κ : Type u) [Field κ] :
    Valuation.Compatible
      ((ValuationRing.valuation (RationalExponentSeries κ)
          (FractionRing (RationalExponentSeries κ))).comap
        (algebraMap (RationalExponentSeries κ)
          (FractionRing (RationalExponentSeries κ)))) :=
  sorry

/-- The series ring has rank at most one; its value group is `ℚ`. -/
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

end RationalExponentSeries
