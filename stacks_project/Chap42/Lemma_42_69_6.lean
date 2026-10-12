/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowGroup.FirstChern.DenominatorProduct
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedCycle.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.MeromorphicSection.ComponentRestriction
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.MeromorphicSection.Denominator.Product.Exact

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.DenominatorProduct

open MeromorphicSection

/- Lemma 42.69.6 (1): the denominator-product inclusion gives the first short exact
sequence. -/
@[stacks 02SW] #check
  (AlgebraicGeometry.Scheme.Modules.DenominatorProduct.inclusion_shortExact :
    ∀ {S X : Scheme.{u}} (p : X ⟶ S)
      [UniversallyCatenary S] [LocallyOfFiniteType p]
      (δ : S → ℤ) [IsDimensionFunction δ] (k : ℤ)
      (ℒ : X.Modules) [Invertible ℒ]
      (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
      (ℱ : X.Modules) [ℱ.IsCoherent]
      (hX : ∀ x, p.relativeDimensionFunction δ x ≤ k + 1)
      (hXEmbedded : X.embeddedPoints = ∅)
      (hFEmbedded : ℱ.embeddedAssociatedPoints = ∅)
      (hFSupport : RingedSpace.moduleSupport ℱ = Set.univ)
      (hs : X.toLocallyRingedSpace.IsRegularMeromorphicSection ℒ s),
      (ShortComplex.cokernelSequence
        (denominatorIdealProduct ℒ s ℱ).arrow).ShortExact)

/- Lemma 42.69.6 (2): the regular meromorphic section induces a denominator-product
morphism `Iℱ ⟶ ℱ ⊗ ℒ`. -/
@[stacks 02SW] #check
  (AlgebraicGeometry.Scheme.Modules.DenominatorProduct.exists_sectionHom :
    ∀ {S X : Scheme.{u}} (p : X ⟶ S)
      [UniversallyCatenary S] [LocallyOfFiniteType p]
      (δ : S → ℤ) [IsDimensionFunction δ] (k : ℤ)
      (ℒ : X.Modules) [Invertible ℒ]
      (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
      (ℱ : X.Modules) [ℱ.IsCoherent]
      (hX : ∀ x, p.relativeDimensionFunction δ x ≤ k + 1)
      (hXEmbedded : X.embeddedPoints = ∅)
      (hFEmbedded : ℱ.embeddedAssociatedPoints = ∅)
      (hFSupport : RingedSpace.moduleSupport ℱ = Set.univ)
      (hs : X.toLocallyRingedSpace.IsRegularMeromorphicSection ℒ s),
      Nonempty (Hom ℒ s ℱ))

/- Lemma 42.69.6 (3): an explicit denominator-product section morphism gives the
second short exact sequence. -/
@[stacks 02SW] #check
  (AlgebraicGeometry.Scheme.Modules.DenominatorProduct.section_shortExact :
    ∀ {S X : Scheme.{u}} (p : X ⟶ S)
      [UniversallyCatenary S] [LocallyOfFiniteType p]
      (δ : S → ℤ) [IsDimensionFunction δ] (k : ℤ)
      (ℒ : X.Modules) [Invertible ℒ]
      (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
      (ℱ : X.Modules) [ℱ.IsCoherent]
      (hX : ∀ x, p.relativeDimensionFunction δ x ≤ k + 1)
      (hXEmbedded : X.embeddedPoints = ∅)
      (hFEmbedded : ℱ.embeddedAssociatedPoints = ∅)
      (hFSupport : RingedSpace.moduleSupport ℱ = Set.univ)
      (hs : X.toLocallyRingedSpace.IsRegularMeromorphicSection ℒ s)
      (σ : Hom ℒ s ℱ),
      (ShortComplex.cokernelSequence σ.hom).ShortExact)

/- Lemma 42.69.6 (4): both coherent quotient sheaves are supported in relative
`δ`-dimension at most `k`. -/
@[stacks 02SW] #check
  (AlgebraicGeometry.Scheme.Modules.DenominatorProduct.quotients_support_le :
    ∀ {S X : Scheme.{u}} (p : X ⟶ S)
      [UniversallyCatenary S] [LocallyOfFiniteType p]
      (δ : S → ℤ) [IsDimensionFunction δ] (k : ℤ)
      (ℒ : X.Modules) [Invertible ℒ]
      (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
      (ℱ : X.Modules) [ℱ.IsCoherent]
      (hX : ∀ x, p.relativeDimensionFunction δ x ≤ k + 1)
      (hXEmbedded : X.embeddedPoints = ∅)
      (hFEmbedded : ℱ.embeddedAssociatedPoints = ∅)
      (hFSupport : RingedSpace.moduleSupport ℱ = Set.univ)
      (hs : X.toLocallyRingedSpace.IsRegularMeromorphicSection ℒ s)
      (σ : Hom ℒ s ℱ),
      (∀ x ∈ RingedSpace.moduleSupport
          (inclusionQuotient p δ k ℒ s ℱ hX hXEmbedded
            hFEmbedded hFSupport hs).obj.obj,
          p.relativeDimensionFunction δ x ≤ k) ∧
        ∀ x ∈ RingedSpace.moduleSupport
          (sectionQuotient p δ k ℒ s ℱ hX hXEmbedded
            hFEmbedded hFSupport hs σ).obj.obj,
          p.relativeDimensionFunction δ x ≤ k)

/- Lemma 42.69.6 (5): the section restricts to a regular meromorphic section on
every irreducible component of relative `δ`-dimension `k + 1`. -/
@[stacks 02SW] #check
  (AlgebraicGeometry.Scheme.Modules.DenominatorProduct.exists_regularComponentRestrictions :
    ∀ {S X : Scheme.{u}} (p : X ⟶ S)
      [UniversallyCatenary S] [LocallyOfFiniteType p]
      (δ : S → ℤ) [IsDimensionFunction δ] (k : ℤ)
      (ℒ : X.Modules) [Invertible ℒ]
      (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
      (ℱ : X.Modules) [ℱ.IsCoherent]
      (hX : ∀ x, p.relativeDimensionFunction δ x ≤ k + 1)
      (hXEmbedded : X.embeddedPoints = ∅)
      (hFEmbedded : ℱ.embeddedAssociatedPoints = ∅)
      (hFSupport : RingedSpace.moduleSupport ℱ = Set.univ)
      (hs : X.toLocallyRingedSpace.IsRegularMeromorphicSection ℒ s),
      Nonempty (∀ C : irreducibleComponents X,
        p.relativeDimensionFunction δ (genericPoints.ofComponent C).1 = k + 1 →
          RegularComponentRestriction ℒ s C))

/- Lemma 42.69.6 (6): the difference of the associated cycles of `Q₂` and `Q₁`
is the multiplicity-weighted sum of the componentwise divisors. -/
@[stacks 02SW] #check
  (AlgebraicGeometry.Scheme.Modules.DenominatorProduct.associatedCycles_sub_eq_componentDivisorSum :
    ∀ {S X : Scheme.{u}} (p : X ⟶ S)
      [UniversallyCatenary S] [LocallyOfFiniteType p]
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
          RegularComponentRestriction ℒ s C),
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
        relativeComponentDivisorSum p δ ℒ s ℱ k r)

/- Lemma 42.69.6 (7): in the Chow group, the quotient-cycle difference is the
first Chern class of `ℒ` capped with the degree-`k + 1` associated cycle of `ℱ`. -/
@[stacks 02SW] #check
  (AlgebraicGeometry.Scheme.Modules.DenominatorProduct.chowClasses_sub_eq_firstChernClassCap :
    ∀ {S X : Scheme.{u}} (p : X ⟶ S)
      [UniversallyCatenary S] [LocallyOfFiniteType p]
      (δ : S → ℤ) [IsDimensionFunction δ] (k : ℤ)
      (ℒ : X.Modules) [Invertible ℒ]
      (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
      (ℱ : X.Modules) [ℱ.IsCoherent]
      (hX : ∀ x, p.relativeDimensionFunction δ x ≤ k + 1)
      (hXEmbedded : X.embeddedPoints = ∅)
      (hFEmbedded : ℱ.embeddedAssociatedPoints = ∅)
      (hFSupport : RingedSpace.moduleSupport ℱ = Set.univ)
      (hs : X.toLocallyRingedSpace.IsRegularMeromorphicSection ℒ s)
      (σ : Hom ℒ s ℱ),
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
          (relativeAssociatedCycle p δ ℱ (k + 1)))

end AlgebraicGeometry.Scheme.Modules.DenominatorProduct
