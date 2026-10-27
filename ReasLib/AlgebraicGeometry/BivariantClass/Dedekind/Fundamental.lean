/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.DedekindDomain.Basic
public import ReasLib.AlgebraicGeometry.ChowCohomology
public import ReasLib.AlgebraicGeometry.ChowGroup.Relative.Cycle
public import ReasLib.AlgebraicGeometry.Scheme.LocalRingProperty.Basic

/-!
# Cap with a fundamental class over a locally Dedekind base

Identity bivariant classes act on the fundamental class in any integer degree.
For a smooth equidimensional scheme over a dimension-one locally Dedekind base,
this action identifies Chow cohomology with Chow homology.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Set
open AlgebraicGeometry.Scheme.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass.Dedekind

/-- Cap of a degree-`p` identity bivariant class with the degree-`d` fundamental class. -/
noncomputable def capFundamental
    {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom] (d p : ℤ)
    (c : ChowCohomology.degree δ X.hom p) :
    RelativeChow δ X (d - p) :=
  c.cap (𝟙 (Over.mk X.hom)) (𝟙 (Over.mk X.hom)) (𝟙 (Over.mk X.hom))
    IsPullback.of_id_snd d (RelativeChow.fundamentalClass δ (Over.mk X.hom) d)

/-- Capping with the fundamental class evaluates the identity-square cap in degree `d`. -/
theorem capFundamental_apply
    {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom] (d p : ℤ)
    (c : ChowCohomology.degree δ X.hom p) :
    capFundamental δ X d p c =
      c.cap (𝟙 (Over.mk X.hom)) (𝟙 (Over.mk X.hom)) (𝟙 (Over.mk X.hom))
        IsPullback.of_id_snd d
        (RelativeChow.fundamentalClass δ (Over.mk X.hom) d) := rfl

/-- The zero identity bivariant class caps to the zero Chow class. -/
theorem capFundamental_zero
    {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom] (d p : ℤ) :
    capFundamental δ X d p (ChowCohomology.zeroClass δ X.hom p) = 0 := sorry

/-- Cap with the degree-`d` fundamental class preserves pointwise addition of
identity bivariant classes. -/
theorem capFundamental_add
    {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom] (d p : ℤ)
    (c c' : ChowCohomology.degree δ X.hom p) :
    capFundamental δ X d p (ChowCohomology.addClass δ X.hom c c') =
      capFundamental δ X d p c + capFundamental δ X d p c' := sorry

/-- On a smooth scheme equidimensional of relative δ-dimension `d` over a
dimension-one locally Dedekind base, cap with the degree-`d` fundamental class
is bijective in every cohomological degree. -/
theorem capFundamental_bijective
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    (h_dim : ∀ component : irreducibleComponents S, topologicalKrullDim component = 1)
    (X : Over S) [Smooth X.hom] (d p : ℤ)
    (hX : ∀ η : genericPoints X.left, X.hom.relativeDimensionFunction δ η.1 = d) :
    Function.Bijective (capFundamental δ X d p) := sorry

end AlgebraicGeometry.BivariantClass.Dedekind
