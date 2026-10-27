/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalScheme.Ideal
public import ReasLib.RingTheory.Valuation.RankOneAdic

/-!
# Valuation-ring obstructions to ideals of definition
-/

@[expose] public section

universe u

noncomputable section

open AlgebraicGeometry IsLocalRing TopologicalRing

namespace AlgebraicGeometry.FormalScheme

/-- The extended maximal ideal of a rank-one valuation ring, complete for a nonzero
principal ideal and with non-finitely-generated maximal ideal, is not an ideal of definition. -/
theorem not_isIdealOfDefinition_ofSpf_maximalIdeal {A : Type u}
    [CommRing A] [IsDomain A] [ValuationRing A] [ValuativeRel A]
    [Valuation.Compatible
      ((ValuationRing.valuation A (FractionRing A)).comap
        (algebraMap A (FractionRing A)))]
    [ValuativeRel.IsRankLeOne A]
    [TopologicalSpace A] [IsTopologicalRing A] {π : A}
    (hπ : π ∈ maximalIdeal A) (hπ0 : π ≠ 0) (h_adic : IsAdic (Ideal.span {π}))
    [IsAdicComplete (Ideal.span {π}) A] (hFG : ¬ (maximalIdeal A).FG)
    (hA : IsAdmissibleRing A) :
    ¬ IsIdealOfDefinition
        (IdealSheafData.ofSpf (.of A) hA (maximalIdeal A)
          (Ideal.isOpen_of_isOpen_subideal
            (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hπ))
            (TopologicalRing.Ideal.isIdealOfDefinition_of_isAdic h_adic).1)) :=
  sorry

end AlgebraicGeometry.FormalScheme
