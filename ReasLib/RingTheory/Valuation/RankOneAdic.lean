/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import ReasLib.RingTheory.Topology.WeaklyAdmissible

@[expose] public section

noncomputable section

universe u

open IsLocalRing

namespace ValuationRing.Adic

/-- The fraction-field valuation of a valuation ring, restricted to the ring. -/
abbrev valuationRingComap (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A] :
    Valuation A (ValuationRing.ValueGroup A (FractionRing A)) :=
  (ValuationRing.valuation A (FractionRing A)).comap (algebraMap A (FractionRing A))

/-- The restricted valuation is the comap along the fraction-field inclusion. -/
theorem valuationRingComap_eq (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A] :
    valuationRingComap A =
      (ValuationRing.valuation A (FractionRing A)).comap
        (algebraMap A (FractionRing A)) :=
  sorry

/-- The non-finitely-generated maximal ideal of a rank-one valuation ring complete
for a nonzero principal ideal in its maximal ideal is a weak ideal of definition. -/
theorem isWeakIdealOfDefinition_maximalIdeal {A : Type u} [CommRing A] [IsDomain A]
    [ValuationRing A] [ValuativeRel A]
    [Valuation.Compatible (valuationRingComap A)] [ValuativeRel.IsRankLeOne A]
    [TopologicalSpace A] [IsTopologicalRing A] {π : A}
    (hπ : π ∈ maximalIdeal A) (hπ0 : π ≠ 0) (h_adic : IsAdic (Ideal.span {π}))
    [IsAdicComplete (Ideal.span {π}) A] (hFG : ¬ (maximalIdeal A).FG) :
    TopologicalRing.Ideal.IsWeakIdealOfDefinition (maximalIdeal A) :=
  sorry

/-- The non-finitely-generated maximal ideal of a rank-one valuation ring complete
for a nonzero principal ideal in its maximal ideal is not an ideal of definition. -/
theorem not_isIdealOfDefinition_maximalIdeal {A : Type u} [CommRing A] [IsDomain A]
    [ValuationRing A] [ValuativeRel A]
    [Valuation.Compatible (valuationRingComap A)] [ValuativeRel.IsRankLeOne A]
    [TopologicalSpace A] [IsTopologicalRing A] {π : A}
    (hπ : π ∈ maximalIdeal A) (hπ0 : π ≠ 0) (h_adic : IsAdic (Ideal.span {π}))
    [IsAdicComplete (Ideal.span {π}) A] (hFG : ¬ (maximalIdeal A).FG) :
    ¬ TopologicalRing.Ideal.IsIdealOfDefinition (maximalIdeal A) :=
  sorry

/-- A valuation ring complete for a principal adic ideal whose radical is maximal
admits a strictly monotone embedding of its value group with zero into `NNReal`. -/
theorem exists_strictMono_emb_of_completePrincipal {R : Type u} [CommRing R] [IsDomain R]
    [ValuationRing R] [ValuativeRel R]
    [Valuation.Compatible (ValuationRing.Adic.valuationRingComap R)]
    [TopologicalSpace R] [IsTopologicalRing R]
    (J : Ideal R) [IsAdicComplete J R] (h_prin : J.IsPrincipal) (h_adic : IsAdic J)
    (h_rad : J.radical = maximalIdeal R) :
    ∃ emb : ValuativeRel.ValueGroupWithZero R →*₀ NNReal, StrictMono emb :=
  sorry

end ValuationRing.Adic
