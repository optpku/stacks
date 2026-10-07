module

public import ReasLib.CategoryTheory.Filtration.Derived.LeftExact.SpectralSequence.Realization.Map.Definition
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Reindexing finite filtered right-derived realization maps

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

namespace Realization.Map

/-- Reindexing preserves compatibility with the chosen associations. -/
@[stacks 015W "reindexing finite filtered right-derived spectral-sequence maps"]
theorem reindexAssociationCompatible {T : A ⥤ₗ B} [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f g : K ⟶ L}
    {S : Realization T K} {R : Realization T L} (h : f = g) (m : Map f S R) :
    FilteredComplex.Association.IsCompatible S.association R.association
      (modelMap T (Resolution.Map.reindex h m.resolutionMap)) m.sequenceMap := sorry

/-- Reindexing an association map preserves its spectral-sequence morphism. -/
@[stacks 015W "reindexing finite filtered right-derived spectral-sequence maps"]
noncomputable def reindexAssociationMap {T : A ⥤ₗ B} [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f g : K ⟶ L}
    {S : Realization T K} {R : Realization T L} (h : f = g) (m : Map f S R) :
    FilteredComplex.Association.Hom S.association R.association
      (modelMap T (Resolution.Map.reindex h m.resolutionMap)) where
  hom := m.sequenceMap
  compatible := reindexAssociationCompatible h m

/-- Reindexing preserves first-page naturality. -/
@[stacks 015W "reindexing finite filtered right-derived spectral-sequence maps"]
theorem reindexPageOne {T : A ⥤ₗ B} [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f g : K ⟶ L}
    {S : Realization T K} {R : Realization T L} (h : f = g) (m : Map f S R) :
    ∀ p q : ℤ,
      CommSq ((m.sequenceMap.hom 1).f (p, q))
        (S.pageOneIso p q).hom (R.pageOneIso p q).hom
        (PageOne.map T g p q) := sorry

/-- Reindexing preserves abutment naturality. -/
@[stacks 015W "reindexing finite filtered right-derived spectral-sequence maps"]
theorem reindexTarget {T : A ⥤ₗ B} [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f g : K ⟶ L}
    {S : Realization T K} {R : Realization T L} (h : f = g) (m : Map f S R) :
    ∀ n : ℤ,
      CommSq (HomologicalComplex.homologyMap
          (FilteredComplex.underlyingMap
            (modelMap T (Resolution.Map.reindex h m.resolutionMap))) n)
        (S.targetIso n).hom (R.targetIso n).hom
        (Abutment.map T g n) := sorry

/-- Reindex a finite right-derived realization map without changing either concrete morphism
component. -/
@[stacks 015W "reindexing finite filtered right-derived spectral-sequence maps"]
noncomputable def reindex {T : A ⥤ₗ B} [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f g : K ⟶ L}
    {S : Realization T K} {R : Realization T L} (h : f = g) (m : Map f S R) :
    Map g S R where
  resolutionMap := Resolution.Map.reindex h m.resolutionMap
  comparisonCompatible :=
    Model.Comparison.IsCompatible.reindex T h m.comparisonCompatible
  associationMap := reindexAssociationMap h m

/-- Reindexing preserves the resolution component. -/
@[simp, stacks 015W "reindexing finite filtered right-derived spectral-sequence maps"]
theorem reindex_resolutionMap {T : A ⥤ₗ B} [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f g : K ⟶ L}
    {S : Realization T K} {R : Realization T L} (h : f = g) (m : Map f S R) :
    (reindex h m).resolutionMap = Resolution.Map.reindex h m.resolutionMap := sorry

/-- Reindexing preserves the filtered-model component. -/
@[simp, stacks 015W "reindexing finite filtered right-derived spectral-sequence maps"]
theorem reindex_filteredMap {T : A ⥤ₗ B} [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f g : K ⟶ L}
    {S : Realization T K} {R : Realization T L} (h : f = g) (m : Map f S R) :
    (reindex h m).filteredMap = m.filteredMap := sorry

/-- Reindexing preserves the spectral-sequence component. -/
@[simp, stacks 015W "reindexing finite filtered right-derived spectral-sequence maps"]
theorem reindex_sequenceMap {T : A ⥤ₗ B} [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f g : K ⟶ L}
    {S : Realization T K} {R : Realization T L} (h : f = g) (m : Map f S R) :
    (reindex h m).sequenceMap = m.sequenceMap := sorry

/-- The association component of a reindexed realization map is the named reindexed
association morphism. -/
@[simp, stacks 015W "reindexed association component of finite filtered right-derived maps"]
theorem reindex_associationMap {T : A ⥤ₗ B} [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f g : K ⟶ L}
    {S : Realization T K} {R : Realization T L} (h : f = g) (m : Map f S R) :
    (reindex h m).associationMap = reindexAssociationMap h m := sorry

/-- Reindexing along reflexivity leaves a realization map unchanged. -/
@[simp, stacks 015W "reindexing finite filtered right-derived spectral-sequence maps"]
theorem reindex_rfl {T : A ⥤ₗ B} [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    {S : Realization T K} {R : Realization T L} (m : Map f S R) :
    reindex rfl m = m := sorry

end Realization.Map

end CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence
