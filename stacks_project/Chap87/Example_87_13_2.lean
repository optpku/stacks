module

public import ReasLib.RingTheory.Valuation.RankOneAdic
public import ReasLib.RingTheory.Valuation.PadicComplexInt
public import ReasLib.RingTheory.Valuation.RationalExponentSeries
public import ReasLib.AlgebraicGeometry.FormalSpectrum.ValuationExample
public import stacks_project.Chap87.Example_87_13_2_FormalSpectrum
public import stacks_project.Chap87.Example_87_13_2_RationalExponentSeries
import StacksCheckRecall

/-!
# Example 87.13.2

A complete valuation ring of rank at most one has a maximal weak ideal of
definition which need not be an ideal of definition. Its fppf sheaf formal
spectrum is affine, and its residue-field morphism is a thickening.

The rank-at-most-one hypothesis is an authorized erratum to the original
unrestricted valuation-ring assertion, which fails in higher rank.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology IsLocalRing
open AlgebraicGeometry AlgebraicGeometry.AffineFormalAlgebraicSpace
open AlgebraicGeometry.ChosenBigFppfSite ValuationRing.Adic RationalExponentSeries

export ValuationRing.Adic (valuationRingComap)

universe u

/- Example 87.13.2: The maximal weak ideal and the affine sheaf formal spectrum with its residue thickening. -/
@[stacks 0CB8] #check (AlgebraicGeometry.AffineFormalAlgebraicSpace.valuationRing_formalSpectrum :
  ∀ {A : Type u} [CommRing A] [IsDomain A]
    [ValuationRing A] [ValuativeRel A]
    [Valuation.Compatible (ValuationRing.Adic.valuationRingComap A)]
    [ValuativeRel.IsRankLeOne A]
    [TopologicalSpace A] [TopologicalRing.IsWeaklyAdmissibleRing A]
    {π : A} (hπ : π ∈ maximalIdeal A)
    (hπ0 : π ≠ 0) (h_adic : IsAdic (Ideal.span {π}))
    [IsAdicComplete (Ideal.span {π}) A] (hFG : ¬ (maximalIdeal A).FG)
    {base : Scheme.{u}} (structureHom : Spec (.of A) ⟶ base)
    [HasWeakSheafify (full.bigTopology base) (Type (u + 1))]
    [HasPullbacks (Sheaf (full.bigTopology base) (Type (u + 1)))],
    TopologicalRing.Ideal.IsWeakIdealOfDefinition (maximalIdeal A) ∧
      ¬ TopologicalRing.Ideal.IsIdealOfDefinition (maximalIdeal A) ∧
      IsAffineFormalAlgebraicSpace (FppfFormalSpectrum.spf A structureHom) ∧
      FppfFormalSpectrum.thickening base
        (FppfFormalSpectrum.specResidue A structureHom
          (ValuationRing.Adic.isWeakIdealOfDefinition_maximalIdeal hπ hπ0 h_adic hFG)))

#check (PadicComplexInt.«example» :
  ∀ (p : ℕ) [Fact p.Prime],
    (p : PadicComplexInt p) ∈ maximalIdeal (PadicComplexInt p) ∧
      (p : PadicComplexInt p) ≠ 0 ∧ ¬ (maximalIdeal (PadicComplexInt p)).FG)

#check (RationalExponentSeries.«example» :
  ∀ (κ : Type u) [Field κ],
    t κ ∈ maximalIdeal (RationalExponentSeries κ) ∧
      t κ ≠ 0 ∧ ¬ (maximalIdeal (RationalExponentSeries κ)).FG)
