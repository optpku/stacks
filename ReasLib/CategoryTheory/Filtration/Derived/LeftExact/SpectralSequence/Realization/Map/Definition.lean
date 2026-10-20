/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.LeftExact.SpectralSequence.Realization.Object
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Maps of finite filtered right-derived realizations

This file is a reusable leaf of the finite filtered right-derived spectral-sequence API.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape
open CochainComplex.FilteredInjectivePlus

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence

variable {A : Type u₁} {B : Type u₂}
  [_root_.CategoryTheory.Category.{v₁} A]
  [_root_.CategoryTheory.Category.{v₂} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{w} B]

namespace Realization

/-- A map of finite right-derived realizations retaining the map of chosen strict resolutions
and its induced spectral-sequence morphism. -/
@[stacks 015W "map of finite filtered right-derived spectral sequences"]
structure Map {T : A ⥤ₗ B} [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} (f : K ⟶ L)
    (S : Realization T K) (R : Realization T L) where
  /-- The morphism between the chosen strict filtered-injective resolutions. -/
  resolutionMap : Resolution.Map f S.resolution R.resolution
  /-- Naturality of the selected model cohomology comparisons. -/
  comparisonCompatible :
    Model.Comparison.IsCompatible T resolutionMap S.comparison R.comparison
  /-- The association-compatible map of spectral sequences. -/
  associationMap : FilteredComplex.Association.Hom S.association R.association
    (modelMap T resolutionMap)

/-- The filtered-model component of a finite right-derived realization map. -/
@[stacks 015W "filtered component of a finite right-derived realization map"]
noncomputable abbrev Map.filteredMap {T : A ⥤ₗ B} [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    {S : Realization T K} {R : Realization T L} (m : Map f S R) :
    S.filtered ⟶ R.filtered :=
  modelMap T m.resolutionMap

/-- The spectral-sequence component of a finite right-derived realization map. -/
@[stacks 015W "spectral-sequence component of a finite right-derived realization map"]
noncomputable abbrev Map.sequenceMap {T : A ⥤ₗ B} [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    {S : Realization T K} {R : Realization T L} (m : Map f S R) :
    S.sequence ⟶ R.sequence :=
  m.associationMap.hom

namespace Map

/-- Build a finite realization map from explicit resolution, comparison, and association
compatibility data. -/
@[stacks 015W "constructor for a finite filtered right-derived realization map"]
def ofResolutionMap {T : A ⥤ₗ B} [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    {S : Realization T K} {R : Realization T L}
    (m : Resolution.Map f S.resolution R.resolution)
    (hm : Model.Comparison.IsCompatible T m S.comparison R.comparison)
    (a : FilteredComplex.Association.Hom S.association R.association (modelMap T m)) :
    Map f S R where
  resolutionMap := m
  comparisonCompatible := hm
  associationMap := a

/-- A resolution map compatible with the chosen model comparisons lifts to a finite realization
map after choosing the propositionally unique compatible association morphism. -/
@[stacks 015W "existence of a finite filtered right-derived realization map"]
theorem nonemptyOfResolutionMap {T : A ⥤ₗ B} [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    {S : Realization T K} {R : Realization T L}
    (m : Resolution.Map f S.resolution R.resolution)
    (hm : Model.Comparison.IsCompatible T m S.comparison R.comparison) :
    Nonempty (Map f S R) := sorry

/-- Naturality of the derived first-page comparison for a finite realization map. -/
@[stacks 015W "naturality square for the finite filtered right-derived first page"]
theorem pageOneSq {T : A ⥤ₗ B} [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    {S : Realization T K} {R : Realization T L} (m : Map f S R) :
    ∀ p q : ℤ,
      CommSq ((m.associationMap.hom.hom 1).f (p, q))
        (S.pageOneIso p q).hom (R.pageOneIso p q).hom
        (PageOne.map T f p q) := sorry

/-- Naturality of the derived abutment comparison for a finite realization map. -/
@[stacks 015W "naturality square for the finite filtered right-derived abutment"]
theorem targetSq {T : A ⥤ₗ B} [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    {S : Realization T K} {R : Realization T L} (m : Map f S R) :
    ∀ n : ℤ,
      CommSq
        (HomologicalComplex.homologyMap
          (FilteredComplex.underlyingMap (modelMap T m.resolutionMap)) n)
        (S.targetIso n).hom (R.targetIso n).hom (Abutment.map T f n) := sorry

/-- Maps of finite right-derived realizations are determined by their morphisms between the
chosen strict filtered-injective resolutions. -/
@[ext, stacks 015W "extensionality of maps of finite filtered right-derived spectral sequences"]
theorem ext {T : A ⥤ₗ B} [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    {S : Realization T K} {R : Realization T L} {m n : Map f S R}
    (h : m.resolutionMap.hom = n.resolutionMap.hom) : m = n := sorry

/-- Equation form of first-page naturality for a finite right-derived realization map. -/
@[reassoc, stacks 015W "finite filtered right-derived first-page naturality"]
theorem pageOne_hom {T : A ⥤ₗ B} [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    {S : Realization T K} {R : Realization T L} (m : Map f S R) (p q : ℤ) :
    (m.sequenceMap.hom 1).f (p, q) ≫ (R.pageOneIso p q).hom =
      (S.pageOneIso p q).hom ≫ PageOne.map T f p q := sorry

/-- Equation form of abutment naturality for a finite right-derived realization map. -/
@[reassoc, stacks 015W "finite filtered right-derived abutment naturality"]
theorem target_hom {T : A ⥤ₗ B} [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    {S : Realization T K} {R : Realization T L} (m : Map f S R) (n : ℤ) :
    HomologicalComplex.homologyMap (FilteredComplex.underlyingMap m.filteredMap) n ≫
        (R.targetIso n).hom =
      (S.targetIso n).hom ≫ Abutment.map T f n := sorry

/-- Inverse naturality of the first-page comparison for a finite right-derived realization map. -/
@[reassoc, stacks 015W "inverse naturality of the finite filtered right-derived first page"]
theorem pageOne_inv_naturality {T : A ⥤ₗ B} [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    {S : Realization T K} {R : Realization T L} (m : Map f S R) (p q : ℤ) :
    PageOne.map T f p q ≫ (R.pageOneIso p q).inv =
      (S.pageOneIso p q).inv ≫ (m.sequenceMap.hom 1).f (p, q) := sorry

/-- Inverse naturality of the abutment comparison for a finite right-derived realization map. -/
@[reassoc, stacks 015W "inverse naturality of the finite filtered right-derived abutment"]
theorem target_inv_naturality {T : A ⥤ₗ B} [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    {S : Realization T K} {R : Realization T L} (m : Map f S R) (n : ℤ) :
    Abutment.map T f n ≫ (R.targetIso n).inv =
      (S.targetIso n).inv ≫
        HomologicalComplex.homologyMap (FilteredComplex.underlyingMap m.filteredMap) n := sorry

/-- Conjugating the map on derived graded-piece cohomology by the selected first-page
comparisons recovers the underlying page component. -/
@[reassoc, stacks 015W "computation of the finite filtered first-page map"]
theorem pageOne_naturality_inv {T : A ⥤ₗ B} [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    {S : Realization T K} {R : Realization T L} (m : Map f S R) (p q : ℤ) :
    (S.pageOneIso p q).hom ≫ PageOne.map T f p q ≫
        (R.pageOneIso p q).inv =
      (m.sequenceMap.hom 1).f (p, q) := sorry

/-- Conjugating the finite filtered model page map by the inverse comparisons recovers the
derived first-page map. -/
@[reassoc, stacks 015W "target-map computation of a finite filtered right-derived first page"]
theorem pageOne_target_map {T : A ⥤ₗ B} [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    {S : Realization T K} {R : Realization T L} (m : Map f S R) (p q : ℤ) :
    (S.pageOneIso p q).inv ≫
        (m.sequenceMap.hom 1).f (p, q) ≫
      (R.pageOneIso p q).hom =
      PageOne.map T f p q := sorry

/-- Conjugating the derived abutment map by the selected comparisons recovers the homology map
of the finite filtered model. -/
@[reassoc, stacks 015W "computation of the finite filtered abutment map"]
theorem target_naturality_inv {T : A ⥤ₗ B} [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    {S : Realization T K} {R : Realization T L} (m : Map f S R) (n : ℤ) :
    (S.targetIso n).hom ≫ Abutment.map T f n ≫
        (R.targetIso n).inv =
      HomologicalComplex.homologyMap (FilteredComplex.underlyingMap m.filteredMap) n := sorry

/-- Conjugating the finite filtered model map by the inverse abutment comparisons recovers the
derived abutment map. -/
@[reassoc, stacks 015W "target-map computation of a finite filtered right-derived abutment"]
theorem target_map {T : A ⥤ₗ B} [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    {S : Realization T K} {R : Realization T L} (m : Map f S R) (n : ℤ) :
    (S.targetIso n).inv ≫
        HomologicalComplex.homologyMap (FilteredComplex.underlyingMap m.filteredMap) n ≫
      (R.targetIso n).hom =
      Abutment.map T f n := sorry

end Map
end Realization

end CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence
