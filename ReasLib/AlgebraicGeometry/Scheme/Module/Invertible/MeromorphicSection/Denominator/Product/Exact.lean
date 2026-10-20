/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent.Closure
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Coherent.SupportDimension
public import ReasLib.AlgebraicGeometry.Scheme.EmbeddedPoints
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Tensor
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.MeromorphicSection.Denominator.Product
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DimensionFunction
public import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary
public import ReasLib.Topology.Specialization.Dimension
public import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# Exact sequences from denominator products

This file packages denominator-product section morphisms and the coherent,
dimension-bounded cokernels in their two associated short exact sequences.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.DenominatorProduct

variable {X : Scheme.{u}}

/-- A concrete denominator-product morphism `Iℱ ⟶ ℱ ⊗ ℒ`, together with its
factorization, injectivity, and cokernel-support properties. -/
structure Hom (ℒ : X.Modules) [Invertible ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ) (ℱ : X.Modules) where
  hom : Subobject.underlying.obj (denominatorIdealProduct ℒ s ℱ) ⟶ ℱ ⊗ ℒ
  factor : denominatorIdealProductFactor ℒ s ℱ ≫ hom =
    denominatorSectionTensorMap ℒ s ℱ
  mono : Mono hom
  cokernelSupport : RingedSpace.moduleSupport (cokernel hom) ⊆ denominatorSupport ℒ s

namespace Hom

/-- Build a denominator-product morphism from an explicitly supplied map and
its laws. -/
def ofMap (ℒ : X.Modules) [Invertible ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ) (ℱ : X.Modules)
    (hom : Subobject.underlying.obj (denominatorIdealProduct ℒ s ℱ) ⟶ ℱ ⊗ ℒ)
    (factor : denominatorIdealProductFactor ℒ s ℱ ≫ hom =
      denominatorSectionTensorMap ℒ s ℱ)
    (mono : Mono hom)
    (cokernelSupport : RingedSpace.moduleSupport (cokernel hom) ⊆ denominatorSupport ℒ s) :
    Hom ℒ s ℱ :=
  { hom, factor, mono, cokernelSupport }

/-- The morphism stored by `ofMap` is the supplied denominator-product map. -/
theorem ofMap_hom (ℒ : X.Modules) [Invertible ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ) (ℱ : X.Modules)
    (hom : Subobject.underlying.obj (denominatorIdealProduct ℒ s ℱ) ⟶ ℱ ⊗ ℒ)
    (factor : denominatorIdealProductFactor ℒ s ℱ ≫ hom =
      denominatorSectionTensorMap ℒ s ℱ)
    (mono : Mono hom)
    (cokernelSupport : RingedSpace.moduleSupport (cokernel hom) ⊆ denominatorSupport ℒ s) :
    (ofMap ℒ s ℱ hom factor mono cokernelSupport).hom = hom := sorry

/-- The defining properties of a denominator-product morphism. -/
theorem spec (ℒ : X.Modules) [Invertible ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ) (ℱ : X.Modules)
    (σ : Hom ℒ s ℱ) :
    denominatorIdealProductFactor ℒ s ℱ ≫ σ.hom =
        denominatorSectionTensorMap ℒ s ℱ ∧
      Mono σ.hom ∧
      RingedSpace.moduleSupport (cokernel σ.hom) ⊆ denominatorSupport ℒ s := sorry

/-- A denominator-product morphism with the prescribed factorization is unique. -/
theorem unique (ℒ : X.Modules) [Invertible ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ) (ℱ : X.Modules)
    (σ τ : Hom ℒ s ℱ) : σ = τ := sorry

end Hom

/-- The cokernel of the denominator-product inclusion is coherent. -/
theorem inclusionQuotient_isCoherent
    [IsLocallyNoetherian X] (ℒ : X.Modules) [Invertible ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (ℱ : X.Modules) [ℱ.IsCoherent]
    (hs : X.toLocallyRingedSpace.IsRegularMeromorphicSection ℒ s) :
    (cokernel (denominatorIdealProduct ℒ s ℱ).arrow).IsCoherent := sorry

/-- The cokernel of a denominator-product section morphism is coherent. -/
theorem sectionQuotient_isCoherent
    [IsLocallyNoetherian X] (ℒ : X.Modules) [Invertible ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (ℱ : X.Modules) [ℱ.IsCoherent]
    (hs : X.toLocallyRingedSpace.IsRegularMeromorphicSection ℒ s)
    (σ : Hom ℒ s ℱ) :
    (cokernel σ.hom).IsCoherent := sorry

/-- Under the usual dimension, support, and regularity hypotheses, the
denominator-inclusion cokernel has relative support dimension at most `k`. -/
theorem inclusionQuotient_support
    {S : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] (k : ℤ)
    (ℒ : X.Modules) [Invertible ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (ℱ : X.Modules) [ℱ.IsCoherent]
    (hX : ∀ x, p.relativeDimensionFunction δ x ≤ k + 1)
    (hXEmbedded : X.embeddedPoints = ∅)
    (hFEmbedded : ℱ.embeddedAssociatedPoints = ∅)
    (hFSupport : RingedSpace.moduleSupport ℱ = Set.univ)
    (hs : X.toLocallyRingedSpace.IsRegularMeromorphicSection ℒ s) :
    ∀ x ∈ RingedSpace.moduleSupport
      (cokernel (denominatorIdealProduct ℒ s ℱ).arrow),
      p.relativeDimensionFunction δ x ≤ k := sorry

/-- Under the usual dimension, support, and regularity hypotheses, the
section-morphism cokernel has relative support dimension at most `k`. -/
theorem sectionQuotient_support
    {S : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
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
    ∀ x ∈ RingedSpace.moduleSupport (cokernel σ.hom),
      p.relativeDimensionFunction δ x ≤ k := sorry

/-- The coherent quotient `Q₁`, represented by the cokernel of `Iℱ ⟶ ℱ`. -/
noncomputable def inclusionQuotient
    {S : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] (k : ℤ)
    (ℒ : X.Modules) [Invertible ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (ℱ : X.Modules) [ℱ.IsCoherent]
    (hX : ∀ x, p.relativeDimensionFunction δ x ≤ k + 1)
    (hXEmbedded : X.embeddedPoints = ∅)
    (hFEmbedded : ℱ.embeddedAssociatedPoints = ∅)
    (hFSupport : RingedSpace.moduleSupport ℱ = Set.univ)
    (hs : X.toLocallyRingedSpace.IsRegularMeromorphicSection ℒ s) :
    RingedSpace.CohLE X.toRingedSpace (p.relativeDimensionFunction δ) k :=
  ⟨⟨cokernel (denominatorIdealProduct ℒ s ℱ).arrow,
      @inclusionQuotient_isCoherent X
        (LocallyOfFiniteType.isLocallyNoetherian p) ℒ _ s ℱ _ hs⟩,
    (RingedSpace.Coh.supportDimensionLE_iff
      (p.relativeDimensionFunction δ) k _).2
      (inclusionQuotient_support p δ k ℒ s ℱ hX hXEmbedded
        hFEmbedded hFSupport hs)⟩

/-- The underlying module of `inclusionQuotient` is the canonical cokernel of
the denominator-product inclusion. -/
theorem inclusionQuotient_obj
    {S : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] (k : ℤ)
    (ℒ : X.Modules) [Invertible ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (ℱ : X.Modules) [ℱ.IsCoherent]
    (hX : ∀ x, p.relativeDimensionFunction δ x ≤ k + 1)
    (hXEmbedded : X.embeddedPoints = ∅)
    (hFEmbedded : ℱ.embeddedAssociatedPoints = ∅)
    (hFSupport : RingedSpace.moduleSupport ℱ = Set.univ)
    (hs : X.toLocallyRingedSpace.IsRegularMeromorphicSection ℒ s) :
    (inclusionQuotient p δ k ℒ s ℱ hX hXEmbedded hFEmbedded hFSupport hs).obj.obj =
      cokernel (denominatorIdealProduct ℒ s ℱ).arrow := sorry

/-- The coherent quotient `Q₂`, represented by the cokernel of an explicit
denominator-product section morphism. -/
noncomputable def sectionQuotient
    {S : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
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
    RingedSpace.CohLE X.toRingedSpace (p.relativeDimensionFunction δ) k :=
  ⟨⟨cokernel σ.hom,
      @sectionQuotient_isCoherent X
        (LocallyOfFiniteType.isLocallyNoetherian p) ℒ _ s ℱ _ hs σ⟩,
    (RingedSpace.Coh.supportDimensionLE_iff
      (p.relativeDimensionFunction δ) k _).2
      (sectionQuotient_support p δ k ℒ s ℱ hX hXEmbedded
        hFEmbedded hFSupport hs σ)⟩

/-- The underlying module of `sectionQuotient` is the cokernel of the supplied
section morphism. -/
theorem sectionQuotient_obj
    {S : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
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
    (sectionQuotient p δ k ℒ s ℱ hX hXEmbedded hFEmbedded hFSupport hs σ).obj.obj =
      cokernel σ.hom := sorry

/-- The denominator-product inclusion yields a short exact cokernel sequence. -/
theorem inclusion_shortExact
    {S : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] (k : ℤ)
    (ℒ : X.Modules) [Invertible ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (ℱ : X.Modules) [ℱ.IsCoherent]
    (hX : ∀ x, p.relativeDimensionFunction δ x ≤ k + 1)
    (hXEmbedded : X.embeddedPoints = ∅)
    (hFEmbedded : ℱ.embeddedAssociatedPoints = ∅)
    (hFSupport : RingedSpace.moduleSupport ℱ = Set.univ)
    (hs : X.toLocallyRingedSpace.IsRegularMeromorphicSection ℒ s) :
    (ShortComplex.cokernelSequence
      (denominatorIdealProduct ℒ s ℱ).arrow).ShortExact := sorry

/-- A regular meromorphic section induces a denominator-product morphism
`Iℱ ⟶ ℱ ⊗ ℒ`. -/
theorem exists_sectionHom
    {S : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] (k : ℤ)
    (ℒ : X.Modules) [Invertible ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (ℱ : X.Modules) [ℱ.IsCoherent]
    (hX : ∀ x, p.relativeDimensionFunction δ x ≤ k + 1)
    (hXEmbedded : X.embeddedPoints = ∅)
    (hFEmbedded : ℱ.embeddedAssociatedPoints = ∅)
    (hFSupport : RingedSpace.moduleSupport ℱ = Set.univ)
    (hs : X.toLocallyRingedSpace.IsRegularMeromorphicSection ℒ s) :
    Nonempty (Hom ℒ s ℱ) := sorry

/-- An explicit denominator-product section morphism yields a short exact
cokernel sequence. -/
theorem section_shortExact
    {S : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
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
    (ShortComplex.cokernelSequence σ.hom).ShortExact := sorry

/-- The two coherent denominator-product quotients have relative support
dimension at most `k`. -/
theorem quotients_support_le
    {S : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
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
    (∀ x ∈ RingedSpace.moduleSupport
        (inclusionQuotient p δ k ℒ s ℱ hX hXEmbedded
          hFEmbedded hFSupport hs).obj.obj,
        p.relativeDimensionFunction δ x ≤ k) ∧
      ∀ x ∈ RingedSpace.moduleSupport
        (sectionQuotient p δ k ℒ s ℱ hX hXEmbedded
          hFEmbedded hFSupport hs σ).obj.obj,
        p.relativeDimensionFunction δ x ≤ k := sorry

end AlgebraicGeometry.Scheme.Modules.DenominatorProduct
