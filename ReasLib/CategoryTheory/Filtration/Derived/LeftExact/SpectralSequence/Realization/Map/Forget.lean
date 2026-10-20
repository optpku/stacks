/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.LeftExact.SpectralSequence.Realization.Forget
public import ReasLib.CategoryTheory.Filtration.Derived.LeftExact.SpectralSequence.Realization.Map.Category
public import ReasLib.CategoryTheory.Filtration.Derived.LeftExact.SpectralSequence.Realization.Map.IsIso
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Forgetting maps of finite right-derived realizations

These leaves forget construction-specific finite-resolution data while retaining the generic
filtered spectral-sequence interfaces used by downstream applications.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape
open CochainComplex.FilteredInjectivePlus

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Category.{v₂} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{w} B]

/-- A finite right-derived realization map induces a generic realization map retaining the
functorial abutment square. -/
@[stacks 015W "generic map with abutment of finite right-derived realizations"]
noncomputable def Realization.Map.toWithAbutmentMap
    {T : A ⥤ₗ B} [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    {S : Realization T K} {R : Realization T L} (m : Realization.Map f S R) :
    FilteredComplex.SpectralSequence.Realization.WithAbutment.Map
      (Abutment.functor T) f S.toWithAbutment R.toWithAbutment where
  toRealizationMap :=
    { filteredMap := m.filteredMap
      sequenceMap := m.sequenceMap
      compatible := m.associationMap.compatible }
  abutmentSq := m.targetSq

/-- Forgetting the abutment square from `toWithAbutmentMap` gives the generic realization map.
This compatibility abbreviation keeps the older interface without duplicating map data. -/
@[stacks 015W "generic map of finite right-derived realizations"]
noncomputable abbrev Realization.Map.toFilteredMap
    {T : A ⥤ₗ B} [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    {S : Realization T K} {R : Realization T L} (m : Realization.Map f S R) :
    FilteredComplex.SpectralSequence.Realization.Map
      S.toFilteredRealization R.toFilteredRealization :=
  m.toWithAbutmentMap.toRealizationMap

namespace Realization.Map.toWithAbutmentMap

/-- The generic realization map underlying `toWithAbutmentMap` is `toFilteredMap`. -/
@[simp, stacks 015W "generic map with abutment of finite right-derived realizations"]
theorem toRealizationMap
    {T : A ⥤ₗ B} [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    {S : Realization T K} {R : Realization T L} (m : Realization.Map f S R) :
    m.toWithAbutmentMap.toRealizationMap = m.toFilteredMap := sorry

/-- The abutment-preserving conversion retains the finite realization's filtered component. -/
@[simp, stacks 015W "filtered component of a generic realization map with abutment"]
theorem filteredMap
    {T : A ⥤ₗ B} [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    {S : Realization T K} {R : Realization T L} (m : Realization.Map f S R) :
    m.toWithAbutmentMap.filteredMap = m.filteredMap := sorry

/-- The abutment-preserving conversion retains the finite realization's spectral-sequence
component. -/
@[simp, stacks 015W "spectral-sequence component of a generic realization map with abutment"]
theorem sequenceMap
    {T : A ⥤ₗ B} [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    {S : Realization T K} {R : Realization T L} (m : Realization.Map f S R) :
    m.toWithAbutmentMap.sequenceMap = m.sequenceMap := sorry

end Realization.Map.toWithAbutmentMap

namespace Realization.Map.toFilteredMap

/-- The generic map conversion retains the finite realization's filtered component. -/
@[simp, stacks 015W "filtered component of a generic finite realization map"]
theorem filteredMap
    {T : A ⥤ₗ B} [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    {S : Realization T K} {R : Realization T L} (m : Realization.Map f S R) :
    m.toFilteredMap.filteredMap = m.filteredMap := sorry

/-- The generic map conversion retains the finite realization's sequence component. -/
@[simp, stacks 015W "spectral-sequence component of a generic finite realization map"]
theorem sequenceMap
    {T : A ⥤ₗ B} [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    {S : Realization T K} {R : Realization T L} (m : Realization.Map f S R) :
    m.toFilteredMap.sequenceMap = m.sequenceMap := sorry

/-- The association morphism of a converted generic map has the same spectral-sequence
component as the finite association map. -/
@[simp, stacks 015W "association component of a generic finite realization map"]
theorem association_hom
    {T : A ⥤ₗ B} [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    {S : Realization T K} {R : Realization T L} (m : Realization.Map f S R) :
    m.toFilteredMap.toAssociationHom.hom = m.associationMap.hom := sorry

/-- The association morphism of a converted map is the original association morphism. -/
@[simp, stacks 015W "association morphism under generic finite realization conversion"]
theorem toAssociationHom
    {T : A ⥤ₗ B} [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    {S : Realization T K} {R : Realization T L} (m : Realization.Map f S R) :
    m.toFilteredMap.toAssociationHom = m.associationMap := sorry

end Realization.Map.toFilteredMap

namespace Realization.Map.toWithAbutmentMap

/-- The association morphism of the abutment-preserving conversion is the original finite
association morphism. -/
@[simp, stacks 015W "association morphism under abutment-preserving finite realization conversion"]
theorem toAssociationHom
    {T : A ⥤ₗ B} [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    {S : Realization T K} {R : Realization T L} (m : Realization.Map f S R) :
    m.toWithAbutmentMap.toAssociationHom = m.associationMap := sorry

end Realization.Map.toWithAbutmentMap

namespace Realization.Map.toFilteredMap

/-- Converted maps are equal whenever their finite filtered-model components are equal. -/
@[stacks 015W "extensionality after generic finite realization conversion"]
theorem eq_of_filteredMap_eq
    {T : A ⥤ₗ B} [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    {S : Realization T K} {R : Realization T L}
    {m n : Realization.Map f S R} (h : m.filteredMap = n.filteredMap) :
    m.toFilteredMap = n.toFilteredMap := sorry

end Realization.Map.toFilteredMap

namespace Realization.Map.toWithAbutmentMap

/-- Converting the finite identity map agrees with the generic identity map retaining the
abutment comparison. -/
@[simp, stacks 015W "identity under abutment-preserving finite realization conversion"]
theorem id
    {T : A ⥤ₗ B} [EnoughInjectives A]
    {K : CochainComplex.Plus (FilteredObject.Finite.category A)}
    (S : Realization T K) :
    (Realization.Map.id S).toWithAbutmentMap =
      FilteredComplex.SpectralSequence.Realization.WithAbutment.Map.id
        (Abutment.functor T) S.toWithAbutment := sorry

end Realization.Map.toWithAbutmentMap

namespace Realization.Map.toFilteredMap

/-- Converting the finite identity map agrees with the generic identity map. -/
@[simp, stacks 015W "identity map under generic finite realization conversion"]
theorem id
    {T : A ⥤ₗ B} [EnoughInjectives A]
    {K : CochainComplex.Plus (FilteredObject.Finite.category A)}
    (S : Realization T K) :
    (Realization.Map.id S).toFilteredMap =
      FilteredComplex.SpectralSequence.Realization.Map.id S.toFilteredRealization := sorry

/-- Converting a composite finite map agrees with composing the converted generic maps. -/
@[simp, stacks 015W "composition under generic finite realization conversion"]
theorem comp
    {T : A ⥤ₗ B} [EnoughInjectives A]
    {K L M : CochainComplex.Plus (FilteredObject.Finite.category A)}
    {f : K ⟶ L} {g : L ⟶ M}
    {S : Realization T K} {R : Realization T L} {U : Realization T M}
    (m : Realization.Map f S R) (n : Realization.Map g R U) :
    (Realization.Map.comp m n).toFilteredMap =
      FilteredComplex.SpectralSequence.Realization.Map.comp
        m.toFilteredMap n.toFilteredMap := sorry

end Realization.Map.toFilteredMap

namespace Realization.Map.toWithAbutmentMap

/-- Converting a composite finite map agrees with composing the generic maps retaining the
abutment comparisons. -/
@[simp, stacks 015W "composition under abutment-preserving finite realization conversion"]
theorem comp
    {T : A ⥤ₗ B} [EnoughInjectives A]
    {K L M : CochainComplex.Plus (FilteredObject.Finite.category A)}
    {f : K ⟶ L} {g : L ⟶ M}
    {S : Realization T K} {R : Realization T L} {U : Realization T M}
    (m : Realization.Map f S R) (n : Realization.Map g R U) :
    (Realization.Map.comp m n).toWithAbutmentMap =
      FilteredComplex.SpectralSequence.Realization.WithAbutment.Map.comp
        (Abutment.functor T) m.toWithAbutmentMap n.toWithAbutmentMap := sorry

end Realization.Map.toWithAbutmentMap

namespace Realization.Map.toFilteredMap

/-- Reindexing a finite map does not change its generic realization map. -/
@[simp, stacks 015W "reindexing under generic finite realization conversion"]
theorem reindex
    {T : A ⥤ₗ B} [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f g : K ⟶ L}
    {S : Realization T K} {R : Realization T L} (h : f = g)
    (m : Realization.Map f S R) :
    (Realization.Map.reindex h m).toFilteredMap = m.toFilteredMap := sorry

end Realization.Map.toFilteredMap

namespace Realization.Map.toWithAbutmentMap

/-- Reindexing a finite map commutes with the generic conversion retaining the abutment
comparison. -/
@[simp, stacks 015W "reindexing under abutment-preserving finite realization conversion"]
theorem reindex
    {T : A ⥤ₗ B} [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f g : K ⟶ L}
    {S : Realization T K} {R : Realization T L} (h : f = g)
    (m : Realization.Map f S R) :
    (Realization.Map.reindex h m).toWithAbutmentMap =
      FilteredComplex.SpectralSequence.Realization.WithAbutment.Map.reindex
        (Abutment.functor T) h m.toWithAbutmentMap := sorry

end Realization.Map.toWithAbutmentMap

end CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence
