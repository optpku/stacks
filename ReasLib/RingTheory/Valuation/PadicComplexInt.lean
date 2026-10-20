/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.NumberTheory.Padics.Complex
public import ReasLib.RingTheory.Valuation.RankOneAdic

@[expose] public section

noncomputable section

open IsLocalRing ValuationRing.Adic

namespace PadicComplexInt

/-- The inherited norm topology on the `p`-adic complex integers is adic for `(p)`. -/
theorem isAdic_span_p (p : ℕ) [Fact p.Prime] :
    IsAdic (Ideal.span {(p : PadicComplexInt p)}) :=
  sorry

/-- The valuative relation induced by restricting the `p`-adic complex valuation. -/
instance instValuativeRel (p : ℕ) [Fact p.Prime] :
    ValuativeRel (PadicComplexInt p) :=
  ValuativeRel.ofValuation <|
    (PadicComplex.valued p).v.comap (algebraMap (PadicComplexInt p) ℂ_[p])

/-- The fraction-field valuation is compatible with the `p`-adic valuative relation. -/
instance instCompatible_valuationRing_comap (p : ℕ) [Fact p.Prime] :
    Valuation.Compatible (valuationRingComap (PadicComplexInt p)) :=
  sorry

/-- The canonical valuative relation on the p-adic complex integers has rank at most one. -/
instance instIsRankLeOne (p : ℕ) [Fact p.Prime] :
    ValuativeRel.IsRankLeOne (PadicComplexInt p) :=
  sorry

/-- The `p`-adic complex integers are complete for the ideal `(p)`. -/
instance instIsAdicComplete_span_p (p : ℕ) [Fact p.Prime] :
    IsAdicComplete (Ideal.span {(p : PadicComplexInt p)}) (PadicComplexInt p) :=
  sorry

/-- The `p`-adic complex integers are weakly admissible in their inherited norm topology. -/
instance instIsWeaklyAdmissibleRing (p : ℕ) [Fact p.Prime] :
    TopologicalRing.IsWeaklyAdmissibleRing (PadicComplexInt p) :=
  sorry

/-- The prime `p` is nonzero and lies in the non-finitely-generated maximal ideal
of the `p`-adic complex integers. -/
theorem «example» (p : ℕ) [Fact p.Prime] :
    (p : PadicComplexInt p) ∈ maximalIdeal (PadicComplexInt p) ∧
      (p : PadicComplexInt p) ≠ 0 ∧ ¬ (maximalIdeal (PadicComplexInt p)).FG :=
  sorry

end PadicComplexInt
