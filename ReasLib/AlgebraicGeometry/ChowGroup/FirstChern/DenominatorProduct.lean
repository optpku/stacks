/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.FirstChern
public import ReasLib.AlgebraicGeometry.ChowGroup.WeilDivisor
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedCycle.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.MeromorphicSection.ComponentRestriction
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.MeromorphicSection.Denominator.Product.Exact
public import ReasLib.RingTheory.LocalRing.DimensionOne.FractionalIdealLength

/-!
# First Chern classes from denominator products

This file forms the multiplicity-weighted sum of componentwise divisors of a
regular meromorphic section and compares it with denominator-product quotient
cycles and first-Chern intersection.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.MeromorphicSection

variable {X : Scheme.{u}}

/-- The divisor cycle of an explicit regular restriction to an irreducible
component, pushed forward from the reduced component closure. -/
noncomputable def relativeComponentDivisorCycle
    {S : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (ℒ : X.Modules) [Invertible ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ) (k : ℤ)
    (C : irreducibleComponents X)
    (hC : p.relativeDimensionFunction δ (genericPoints.ofComponent C).1 = k + 1)
    (r : RegularComponentRestriction ℒ s C) :
    CycleGroup X (p.relativeDimensionFunction δ) k :=
  @WeilDivisor.pointClosureCycle X (LocallyOfFiniteType.isLocallyNoetherian p)
    (p.relativeDimensionFunction δ) inferInstance k
    (genericPoints.ofComponent C).1 hC
    (@Scheme.nonzeroMeromorphicSectionWeilDivisor
      (Scheme.PointClosure.scheme (genericPoints.ofComponent C).1)
      (@Scheme.PointClosure.scheme_isLocallyNoetherian X
        (LocallyOfFiniteType.isLocallyNoetherian p) (genericPoints.ofComponent C).1)
      inferInstance
      ((Scheme.Modules.pullback
        (Scheme.PointClosure.ι (genericPoints.ofComponent C).1)).obj ℒ)
      (Scheme.Modules.Invertible.pullback
        (Scheme.PointClosure.ι (genericPoints.ofComponent C).1) inferInstance)
      r.section_ (RegularComponentRestriction.section_ne_zero ℒ s C r))

/-- Evaluation of a component divisor cycle is evaluation of the pushed-forward
divisor on the reduced component closure. -/
theorem relativeComponentDivisorCycle_apply
    {S : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (ℒ : X.Modules) [Invertible ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ) (k : ℤ)
    (C : irreducibleComponents X)
    (hC : p.relativeDimensionFunction δ (genericPoints.ofComponent C).1 = k + 1)
    (r : RegularComponentRestriction ℒ s C) (x : X) :
    CycleGroup.toAlgebraicCycle (p.relativeDimensionFunction δ) k
        (relativeComponentDivisorCycle p δ ℒ s k C hC r) x =
      AlgebraicCycle.map (Scheme.PointClosure.ι (genericPoints.ofComponent C).1)
        ((Scheme.PointClosure.ι (genericPoints.ofComponent C).1 ≫ p).relativeDimensionFunction δ)
        (p.relativeDimensionFunction δ)
        (@Scheme.nonzeroMeromorphicSectionDivisorCycle
          (Scheme.PointClosure.scheme (genericPoints.ofComponent C).1)
          (@Scheme.PointClosure.scheme_isLocallyNoetherian X
            (LocallyOfFiniteType.isLocallyNoetherian p) (genericPoints.ofComponent C).1)
          inferInstance
          ((Scheme.Modules.pullback
            (Scheme.PointClosure.ι (genericPoints.ofComponent C).1)).obj ℒ)
          (Scheme.Modules.Invertible.pullback
            (Scheme.PointClosure.ι (genericPoints.ofComponent C).1) inferInstance)
          r.section_ (RegularComponentRestriction.section_ne_zero ℒ s C r)) x := sorry

/-- The multiplicity-weighted component divisor terms form a locally finite
family. -/
theorem relativeComponentDivisorTermsLocallyFinite
    {S : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (ℒ : X.Modules) [Invertible ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (ℱ : X.Modules) [ℱ.IsCoherent] (k : ℤ)
    (r : ∀ C : irreducibleComponents X,
      p.relativeDimensionFunction δ (genericPoints.ofComponent C).1 = k + 1 →
        RegularComponentRestriction ℒ s C) :
    LocallyFinite fun C : irreducibleComponents X ↦
      (CycleGroup.toAlgebraicCycle (p.relativeDimensionFunction δ) k
        (if hC : p.relativeDimensionFunction δ (genericPoints.ofComponent C).1 = k + 1 then
          (CycleGroup.toAlgebraicCycle (p.relativeDimensionFunction δ) (k + 1)
            (relativeAssociatedCycle p δ ℱ (k + 1))
            (genericPoints.ofComponent C).1) •
              relativeComponentDivisorCycle p δ ℒ s k C hC (r C hC)
        else 0)).support := sorry

/-- The sum `Σ mᵢ (Xᵢ ⟶ X)∗ div(sᵢ)` formed from explicit regular component
restrictions. -/
noncomputable def relativeComponentDivisorSum
    {S : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (ℒ : X.Modules) [Invertible ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (ℱ : X.Modules) [ℱ.IsCoherent] (k : ℤ)
    (r : ∀ C : irreducibleComponents X,
      p.relativeDimensionFunction δ (genericPoints.ofComponent C).1 = k + 1 →
        RegularComponentRestriction ℒ s C) :
    CycleGroup X (p.relativeDimensionFunction δ) k :=
  CycleGroup.locallyFiniteSum (p.relativeDimensionFunction δ) k
    (fun C : irreducibleComponents X ↦
      if hC : p.relativeDimensionFunction δ (genericPoints.ofComponent C).1 = k + 1 then
        (CycleGroup.toAlgebraicCycle (p.relativeDimensionFunction δ) (k + 1)
          (relativeAssociatedCycle p δ ℱ (k + 1))
          (genericPoints.ofComponent C).1) •
            relativeComponentDivisorCycle p δ ℒ s k C hC (r C hC)
      else 0)
    (relativeComponentDivisorTermsLocallyFinite p δ ℒ s ℱ k r)

/-- Evaluation of the component divisor sum is the corresponding pointwise
finite sum. -/
theorem relativeComponentDivisorSum_apply
    {S : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (ℒ : X.Modules) [Invertible ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (ℱ : X.Modules) [ℱ.IsCoherent] (k : ℤ)
    (r : ∀ C : irreducibleComponents X,
      p.relativeDimensionFunction δ (genericPoints.ofComponent C).1 = k + 1 →
        RegularComponentRestriction ℒ s C) (x : X) :
    CycleGroup.toAlgebraicCycle (p.relativeDimensionFunction δ) k
        (relativeComponentDivisorSum p δ ℒ s ℱ k r) x =
      ∑ᶠ C : irreducibleComponents X,
        CycleGroup.toAlgebraicCycle (p.relativeDimensionFunction δ) k
          (if hC : p.relativeDimensionFunction δ (genericPoints.ofComponent C).1 = k + 1 then
            (CycleGroup.toAlgebraicCycle (p.relativeDimensionFunction δ) (k + 1)
              (relativeAssociatedCycle p δ ℱ (k + 1))
              (genericPoints.ofComponent C).1) •
                relativeComponentDivisorCycle p δ ℒ s k C hC (r C hC)
          else 0) x := sorry

end AlgebraicGeometry.Scheme.Modules.MeromorphicSection

namespace AlgebraicGeometry.Scheme.Modules.DenominatorProduct

open MeromorphicSection

/-- The difference of the associated cycles of the two denominator-product
quotients is the multiplicity-weighted sum of the componentwise divisors. -/
theorem associatedCycles_sub_eq_componentDivisorSum
    {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] (k : ℤ)
    (ℒ : X.Modules) [Invertible ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (ℱ : X.Modules) [ℱ.IsCoherent]
    (hX : ∀ x, p.relativeDimensionFunction δ x ≤ k + 1)
    (hXEmbedded : X.embeddedPoints = ∅)
    (hFEmbedded : ℱ.embeddedAssociatedPoints = ∅)
    (hFSupport : RingedSpace.moduleSupport ℱ = Set.univ)
    (hs : X.toLocallyRingedSpace.IsRegularMeromorphicSection ℒ s)
    (σ : Hom ℒ s ℱ)
    (r : ∀ C : irreducibleComponents X,
      p.relativeDimensionFunction δ (genericPoints.ofComponent C).1 = k + 1 →
        RegularComponentRestriction ℒ s C) :
    @relativeAssociatedCycle X S p inferInstance inferInstance δ inferInstance
        (sectionQuotient p δ k ℒ s ℱ hX hXEmbedded
          hFEmbedded hFSupport hs σ).obj.obj
        (sectionQuotient p δ k ℒ s ℱ hX hXEmbedded
          hFEmbedded hFSupport hs σ).obj.property k -
      @relativeAssociatedCycle X S p inferInstance inferInstance δ inferInstance
        (inclusionQuotient p δ k ℒ s ℱ hX hXEmbedded
          hFEmbedded hFSupport hs).obj.obj
        (inclusionQuotient p δ k ℒ s ℱ hX hXEmbedded
          hFEmbedded hFSupport hs).obj.property k =
      relativeComponentDivisorSum p δ ℒ s ℱ k r := sorry

/-- In the Chow group, the denominator-product quotient-cycle difference is
the first Chern class of `ℒ` capped with the degree-`k + 1` associated cycle of
`ℱ`. -/
theorem chowClasses_sub_eq_firstChernClassCap
    {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] (k : ℤ)
    (ℒ : X.Modules) [Invertible ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (ℱ : X.Modules) [ℱ.IsCoherent]
    (hX : ∀ x, p.relativeDimensionFunction δ x ≤ k + 1)
    (hXEmbedded : X.embeddedPoints = ∅)
    (hFEmbedded : ℱ.embeddedAssociatedPoints = ∅)
    (hFSupport : RingedSpace.moduleSupport ℱ = Set.univ)
    (hs : X.toLocallyRingedSpace.IsRegularMeromorphicSection ℒ s)
    (σ : Hom ℒ s ℱ) :
    @chowClass X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance k
        (@relativeAssociatedCycle X S p inferInstance inferInstance δ inferInstance
            (sectionQuotient p δ k ℒ s ℱ hX hXEmbedded
              hFEmbedded hFSupport hs σ).obj.obj
            (sectionQuotient p δ k ℒ s ℱ hX hXEmbedded
              hFEmbedded hFSupport hs σ).obj.property k -
          @relativeAssociatedCycle X S p inferInstance inferInstance δ inferInstance
            (inclusionQuotient p δ k ℒ s ℱ hX hXEmbedded
              hFEmbedded hFSupport hs).obj.obj
            (inclusionQuotient p δ k ℒ s ℱ hX hXEmbedded
              hFEmbedded hFSupport hs).obj.property k) =
      firstChernClassCap p δ ℒ k
        (relativeAssociatedCycle p δ ℱ (k + 1)) := sorry

end AlgebraicGeometry.Scheme.Modules.DenominatorProduct
