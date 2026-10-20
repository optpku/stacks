/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Valuation.RankOneAdic
public import ReasLib.AlgebraicGeometry.FormalSpectrum.ChosenFppf

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open IsLocalRing ValuationRing.Adic AlgebraicGeometry.ChosenBigFppfSite

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

/-- A complete rank-at-most-one valuation ring with non-finitely-generated maximal ideal
has a maximal weak ideal which is not an ideal of definition, an affine sheaf formal
spectrum, and a thickening from its residue-field spectrum. -/
theorem valuationRing_formalSpectrum {A : Type u} [CommRing A] [IsDomain A]
    [ValuationRing A] [ValuativeRel A]
    [Valuation.Compatible (valuationRingComap A)] [ValuativeRel.IsRankLeOne A]
    [TopologicalSpace A] [TopologicalRing.IsWeaklyAdmissibleRing A]
    {π : A} (hπ : π ∈ maximalIdeal A)
    (hπ0 : π ≠ 0) (h_adic : IsAdic (Ideal.span {π}))
    [IsAdicComplete (Ideal.span {π}) A] (hFG : ¬ (maximalIdeal A).FG)
    {base : Scheme.{u}} (structureHom : Spec (.of A) ⟶ base)
    [HasWeakSheafify (full.bigTopology base) (Type (u + 1))]
    [HasPullbacks (Sheaf (full.bigTopology base) (Type (u + 1)))] :
    TopologicalRing.Ideal.IsWeakIdealOfDefinition (maximalIdeal A) ∧
      ¬ TopologicalRing.Ideal.IsIdealOfDefinition (maximalIdeal A) ∧
      IsAffineFormalAlgebraicSpace (FppfFormalSpectrum.spf A structureHom) ∧
      FppfFormalSpectrum.thickening base
        (FppfFormalSpectrum.specResidue A structureHom
          (isWeakIdealOfDefinition_maximalIdeal hπ hπ0 h_adic hFG)) :=
  sorry

end AlgebraicGeometry.AffineFormalAlgebraicSpace
