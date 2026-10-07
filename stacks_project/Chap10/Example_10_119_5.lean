module

public import stacks_project.Chap10.Example_10_119_5.AdjoinedCompletion
public import stacks_project.Chap10.Example_10_119_5.CoefficientFractionField

/-!
# A DVR Whose Finite Overring Has Nonreduced Completion

Let `k` be a field of positive characteristic `p` and infinite degree over `k^p`. The ring of
power series whose coefficients generate a finite extension of `k^p` is a discrete valuation ring
with completion `k[[x]]`. Adjoining any power series outside that ring produces a one-dimensional
Noetherian local domain with nonreduced completion.

@stack 00PB
-/

@[expose] public section

noncomputable section

universe u

open PowerSeries IsLocalRing AdicCompletion
open scoped PthPowerSubfield

namespace PowerSeries.FinitePthPowerCoefficients

variable (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [ExpChar k p]

local notation "A" => finitePthPowerCoefficientSubring k p

/-- Example 10.119.5 (1): the ring `A ⊆ k[[x]]` of power series whose coefficients generate a
finite extension of `k^p` is a discrete valuation ring. -/
@[stacks 00PB]
theorem isDiscreteValuationRing
    (hnfd : ¬ FiniteDimensional (k^[p]) k) :
    IsDiscreteValuationRing ↥A := sorry

/-- Example 10.119.5 (2): the canonical comparison from the maximal-ideal completion of `A` to
`k[[x]]` is bijective. -/
@[stacks 00PB]
theorem completionComparison_bijective
    (hnfd : ¬ FiniteDimensional (k^[p]) k) :
    Function.Bijective
      (finitePthPowerCoefficientSubringCompletionAlgEquivPowerSeries k p) := sorry

/-- Example 10.119.5 (3): the fraction field of `k[[x]]` is purely inseparable over the fraction
field of `A`. -/
@[stacks 00PB]
theorem fractionRing_isPurelyInseparable
    (hnfd : ¬ FiniteDimensional (k^[p]) k) :
    IsPurelyInseparable (FractionRing ↥A) (FractionRing (PowerSeries k)) := sorry

/-- Example 10.119.5 (4): the induced extension from `Frac(A)` to `Frac(k[[x]])` is not
finite-dimensional. -/
@[stacks 00PB]
theorem fractionRing_not_finiteDimensional
    (hnfd : ¬ FiniteDimensional (k^[p]) k) :
    ¬ FiniteDimensional (FractionRing ↥A) (FractionRing (PowerSeries k)) := sorry

namespace Adjoin

variable (f : PowerSeries k)

local notation "R" => finitePthPowerCoefficientAdjoinSubring k p f

/-- Example 10.119.5 (5): for any `f ∉ A`, the ring `R = A[f]` is Noetherian. -/
@[stacks 00PB]
theorem isNoetherianRing
    (hnfd : ¬ FiniteDimensional (k^[p]) k) (hf : f ∉ A) :
    IsNoetherianRing ↥R := sorry

/-- Example 10.119.5 (6): for any `f ∉ A`, the ring `R = A[f]` is local. -/
@[stacks 00PB]
theorem isLocalRing
    (hnfd : ¬ FiniteDimensional (k^[p]) k) (hf : f ∉ A) :
    IsLocalRing ↥R := sorry

/-- Example 10.119.5 (7): for any `f ∉ A`, the ring `R = A[f]`, viewed as a subring of
`k[[x]]`, is a domain. -/
@[stacks 00PB]
theorem isDomain
    (hnfd : ¬ FiniteDimensional (k^[p]) k) (hf : f ∉ A) :
    IsDomain ↥R := sorry

/-- Example 10.119.5 (8): for any `f ∉ A`, the ring `R = A[f]` has Krull dimension one. -/
@[stacks 00PB]
theorem ringKrullDim_eq_one
    (hnfd : ¬ FiniteDimensional (k^[p]) k) (hf : f ∉ A) :
    ringKrullDim ↥R = 1 := sorry

/-- Example 10.119.5 (9): for any `f ∉ A`, the maximal-ideal completion of `R = A[f]` is
nonreduced. -/
@[stacks 00PB]
theorem completion_not_isReduced
    (hnfd : ¬ FiniteDimensional (k^[p]) k) (hf : f ∉ A) :
    ¬ IsReduced (AdicCompletion (maximalIdeal ↥R) ↥R) := sorry

end Adjoin

end PowerSeries.FinitePthPowerCoefficients

#check @PowerSeries.FinitePthPowerCoefficients.isDiscreteValuationRing
#check @PowerSeries.FinitePthPowerCoefficients.completionComparison_bijective
#check @PowerSeries.FinitePthPowerCoefficients.fractionRing_isPurelyInseparable
#check @PowerSeries.FinitePthPowerCoefficients.fractionRing_not_finiteDimensional
#check @PowerSeries.FinitePthPowerCoefficients.Adjoin.isNoetherianRing
#check @PowerSeries.FinitePthPowerCoefficients.Adjoin.isLocalRing
#check @PowerSeries.FinitePthPowerCoefficients.Adjoin.isDomain
#check @PowerSeries.FinitePthPowerCoefficients.Adjoin.ringKrullDim_eq_one
#check @PowerSeries.FinitePthPowerCoefficients.Adjoin.completion_not_isReduced

#print axioms finitePthPowerCoefficientSubringCompletionAlgEquivPowerSeries
