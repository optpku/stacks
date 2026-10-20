/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.ReesAlgebra.BlowupChart.FractionField
public import ReasLib.RingTheory.RingHom.Fiber.Map
public import ReasLib.RingTheory.Valuation.Domination

/-!
# Valuation approximations by affine blowup charts

@stack 052M

This leaf owns the valuation-theoretic interface for affine blowup charts.  The
chart itself and its fraction-field realization remain the algebraic owners;
this file only packages the conditions and the directed-union statements used
when a valuation subring dominates a local domain.
-/

@[expose] public section

universe u v

namespace AffineBlowupChart.Valuation

variable {R : Type u} {K : Type v}
variable [CommRing R] [IsDomain R] [IsLocalRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]

/-- An affine blowup chart is an approximation of a dominating valuation subring when its center
is inside the maximal ideal, is finitely generated, has nontrivial closed fiber, and its canonical
fraction-subring is contained in the valuation subring. -/
@[stacks 052M "valuation approximation by an affine blowup chart"]
structure IsApproximation
    (A : ValuationSubring K) (I : Ideal R)
    (a : AffineBlowupChart.NonzeroParameter I) : Prop where
  /-- The center of the chart is supported at the closed point of `R`. -/
  center_le : I ≤ IsLocalRing.maximalIdeal R
  /-- The chart center is finitely generated. -/
  fg : I.FG
  /-- The chart has a nontrivial closed fiber. -/
  fiber_nontrivial : Nontrivial
    ((AffineBlowupChart.algebraMap I (a : I)).Fiber (IsLocalRing.maximalIdeal R))
  /-- The canonical fraction-field realization lies in the dominating valuation subring. -/
  fractionSubring_le : AffineBlowupChart.fractionSubring (K := K) I a ≤ A.toSubring

/-- A dominating valuation subring gives a nontrivial closed fiber whenever the chart's canonical
fraction subring is contained in it. -/
@[stacks 052M "nontrivial fiber under valuation domination"]
theorem fiber_nontrivial_of_fractionSubring_le
    (A : ValuationSubring K)
    (hA : LocalSubring.range (algebraMap R K) ≤ A.toLocalSubring)
    {I : Ideal R} (a : AffineBlowupChart.NonzeroParameter I)
    (hC : AffineBlowupChart.fractionSubring (K := K) I a ≤ A.toSubring) :
    Nontrivial
      ((AffineBlowupChart.algebraMap I (a : I)).Fiber (IsLocalRing.maximalIdeal R)) := sorry

/-- The affine blowup approximations of a fixed dominating valuation subring are directed by
containment of their canonical fraction subrings. -/
@[stacks 052M "directed affine blowup valuation approximations"]
theorem directed
    (A : ValuationSubring K) {I J : Ideal R}
    {a : AffineBlowupChart.NonzeroParameter I}
    {b : AffineBlowupChart.NonzeroParameter J}
    (hA : LocalSubring.range (algebraMap R K) ≤ A.toLocalSubring)
    (hI : IsApproximation A I a) (hJ : IsApproximation A J b) :
    ∃ (L : Ideal R) (c : AffineBlowupChart.NonzeroParameter L),
      IsApproximation A L c ∧
        AffineBlowupChart.fractionSubring (K := K) I a ≤
          AffineBlowupChart.fractionSubring (K := K) L c ∧
        AffineBlowupChart.fractionSubring (K := K) J b ≤
          AffineBlowupChart.fractionSubring (K := K) L c := sorry

/-- The dominating valuation subring is the supremum of the fraction subrings of its affine
blowup approximations. -/
@[stacks 052M "supremum of affine blowup valuation approximations"]
theorem iSup_eq
    (A : ValuationSubring K)
    (hA : LocalSubring.range (algebraMap R K) ≤ A.toLocalSubring)
    (hm : IsLocalRing.maximalIdeal R ≠ ⊥) :
    A.toSubring =
      ⨆ (I : Ideal R) (a : AffineBlowupChart.NonzeroParameter I),
        ⨆ (_ : IsApproximation A I a),
          AffineBlowupChart.fractionSubring (K := K) I a := sorry

end AffineBlowupChart.Valuation
