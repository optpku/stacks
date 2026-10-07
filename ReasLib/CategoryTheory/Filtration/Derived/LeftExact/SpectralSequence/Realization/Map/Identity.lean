module

public import ReasLib.CategoryTheory.Filtration.Derived.LeftExact.SpectralSequence.Realization.Map.Definition
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Identity maps of finite filtered right-derived realizations

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

/-- The identity resolution and sequence morphisms preserve the chosen association. -/
@[stacks 015W "identity map of a finite filtered right-derived spectral sequence"]
theorem idAssociationCompatible {T : A ⥤ₗ B} [EnoughInjectives A]
    {K : CochainComplex.Plus (FilteredObject.Finite.category A)} (S : Realization T K) :
    FilteredComplex.Association.IsCompatible S.association S.association
      (modelMap T (Resolution.Map.id S.resolution)) (𝟙 S.sequence) := sorry

/-- The association component of the identity finite right-derived realization map. -/
@[stacks 015W "identity map of a finite filtered right-derived spectral sequence"]
noncomputable def idAssociationMap {T : A ⥤ₗ B} [EnoughInjectives A]
    {K : CochainComplex.Plus (FilteredObject.Finite.category A)} (S : Realization T K) :
    FilteredComplex.Association.Hom S.association S.association
      (modelMap T (Resolution.Map.id S.resolution)) where
  hom := 𝟙 S.sequence
  compatible := idAssociationCompatible S

/-- Identity maps commute with the first-page comparison. -/
@[stacks 015W "identity map of a finite filtered right-derived spectral sequence"]
theorem idPageOne {T : A ⥤ₗ B} [EnoughInjectives A]
    {K : CochainComplex.Plus (FilteredObject.Finite.category A)} (S : Realization T K) :
    ∀ p q : ℤ,
      CommSq (((𝟙 S.sequence : S.sequence ⟶ S.sequence).hom 1).f (p, q))
        (S.pageOneIso p q).hom (S.pageOneIso p q).hom
        (PageOne.map T (𝟙 K) p q) := sorry

/-- Identity maps commute with the abutment comparison. -/
@[stacks 015W "identity map of a finite filtered right-derived spectral sequence"]
theorem idTarget {T : A ⥤ₗ B} [EnoughInjectives A]
    {K : CochainComplex.Plus (FilteredObject.Finite.category A)} (S : Realization T K) :
    ∀ n : ℤ,
      CommSq (HomologicalComplex.homologyMap
          (FilteredComplex.underlyingMap
            (modelMap T (Resolution.Map.id S.resolution))) n)
        (S.targetIso n).hom (S.targetIso n).hom
        (Abutment.map T (𝟙 K) n) := sorry

/-- The identity morphism of a finite right-derived realization. -/
@[stacks 015W "identity map of a finite filtered right-derived spectral sequence"]
noncomputable def id {T : A ⥤ₗ B} [EnoughInjectives A]
    {K : CochainComplex.Plus (FilteredObject.Finite.category A)} (S : Realization T K) :
    Map (𝟙 K) S S where
  resolutionMap := Resolution.Map.id S.resolution
  comparisonCompatible := Model.Comparison.IsCompatible.id T S.comparison
  associationMap := idAssociationMap S

/-- The resolution component of the identity realization map is the identity resolution map. -/
@[simp, stacks 015W "identity map of a finite filtered right-derived spectral sequence"]
theorem id_resolutionMap {T : A ⥤ₗ B} [EnoughInjectives A]
    {K : CochainComplex.Plus (FilteredObject.Finite.category A)} (S : Realization T K) :
    (id S).resolutionMap = Resolution.Map.id S.resolution := sorry

/-- The filtered-model component of the identity realization map is the identity. -/
@[simp, stacks 015W "identity map of a finite filtered right-derived spectral sequence"]
theorem id_filteredMap {T : A ⥤ₗ B} [EnoughInjectives A]
    {K : CochainComplex.Plus (FilteredObject.Finite.category A)} (S : Realization T K) :
    (id S).filteredMap = 𝟙 S.filtered := sorry

/-- The spectral-sequence component of the identity realization map is the identity. -/
@[simp, stacks 015W "identity map of a finite filtered right-derived spectral sequence"]
theorem id_sequenceMap {T : A ⥤ₗ B} [EnoughInjectives A]
    {K : CochainComplex.Plus (FilteredObject.Finite.category A)} (S : Realization T K) :
    (id S).sequenceMap = 𝟙 S.sequence := sorry

/-- The association component of the identity realization map is the named identity
association morphism. -/
@[simp, stacks 015W "identity association component of a finite filtered right-derived map"]
theorem id_associationMap {T : A ⥤ₗ B} [EnoughInjectives A]
    {K : CochainComplex.Plus (FilteredObject.Finite.category A)} (S : Realization T K) :
    (id S).associationMap = idAssociationMap S := sorry

end Realization.Map

end CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence
