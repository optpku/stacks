/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.LeftExact.SpectralSequence.Realization.Map.Definition
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Composition of finite filtered right-derived realization maps

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

/-- Composite resolution and sequence morphisms preserve the outer associations. -/
@[stacks 015W "composition of finite filtered right-derived spectral-sequence maps"]
theorem compAssociationCompatible {T : A ⥤ₗ B} [EnoughInjectives A]
    {K L M : CochainComplex.Plus (FilteredObject.Finite.category A)}
    {f : K ⟶ L} {g : L ⟶ M} {S : Realization T K}
    {R : Realization T L} {U : Realization T M} (m : Map f S R) (n : Map g R U) :
    FilteredComplex.Association.IsCompatible S.association U.association
      (modelMap T (Resolution.Map.comp m.resolutionMap n.resolutionMap))
      (m.sequenceMap ≫ n.sequenceMap) := sorry

/-- The association component of a composite finite right-derived realization map. -/
@[stacks 015W "composition of finite filtered right-derived spectral-sequence maps"]
noncomputable def compAssociationMap {T : A ⥤ₗ B} [EnoughInjectives A]
    {K L M : CochainComplex.Plus (FilteredObject.Finite.category A)}
    {f : K ⟶ L} {g : L ⟶ M} {S : Realization T K}
    {R : Realization T L} {U : Realization T M} (m : Map f S R) (n : Map g R U) :
    FilteredComplex.Association.Hom S.association U.association
      (modelMap T (Resolution.Map.comp m.resolutionMap n.resolutionMap)) where
  hom := m.sequenceMap ≫ n.sequenceMap
  compatible := compAssociationCompatible m n

/-- Composite maps commute with the first-page comparison. -/
@[stacks 015W "composition of finite filtered right-derived spectral-sequence maps"]
theorem compPageOne {T : A ⥤ₗ B} [EnoughInjectives A]
    {K L M : CochainComplex.Plus (FilteredObject.Finite.category A)}
    {f : K ⟶ L} {g : L ⟶ M} {S : Realization T K}
    {R : Realization T L} {U : Realization T M} (m : Map f S R) (n : Map g R U) :
    ∀ p q : ℤ,
      CommSq (((m.sequenceMap ≫ n.sequenceMap).hom 1).f (p, q))
        (S.pageOneIso p q).hom (U.pageOneIso p q).hom
        (PageOne.map T (f ≫ g) p q) := sorry

/-- Composite maps commute with the abutment comparison. -/
@[stacks 015W "composition of finite filtered right-derived spectral-sequence maps"]
theorem compTarget {T : A ⥤ₗ B} [EnoughInjectives A]
    {K L M : CochainComplex.Plus (FilteredObject.Finite.category A)}
    {f : K ⟶ L} {g : L ⟶ M} {S : Realization T K}
    {R : Realization T L} {U : Realization T M} (m : Map f S R) (n : Map g R U) :
    ∀ k : ℤ,
      CommSq (HomologicalComplex.homologyMap
          (FilteredComplex.underlyingMap
            (modelMap T (Resolution.Map.comp m.resolutionMap n.resolutionMap))) k)
        (S.targetIso k).hom (U.targetIso k).hom
        (Abutment.map T (f ≫ g) k) := sorry

/-- The composite of finite right-derived realization maps. -/
@[stacks 015W "composition of finite filtered right-derived spectral-sequence maps"]
noncomputable def comp {T : A ⥤ₗ B} [EnoughInjectives A]
    {K L M : CochainComplex.Plus (FilteredObject.Finite.category A)}
    {f : K ⟶ L} {g : L ⟶ M} {S : Realization T K}
    {R : Realization T L} {U : Realization T M} (m : Map f S R) (n : Map g R U) :
    Map (f ≫ g) S U where
  resolutionMap := Resolution.Map.comp m.resolutionMap n.resolutionMap
  comparisonCompatible := Model.Comparison.IsCompatible.comp T
    m.comparisonCompatible n.comparisonCompatible
  associationMap := compAssociationMap m n

/-- The resolution component of a composite realization map is the composite resolution map. -/
@[simp, stacks 015W "composition of finite filtered right-derived spectral-sequence maps"]
theorem comp_resolutionMap {T : A ⥤ₗ B} [EnoughInjectives A]
    {K L M : CochainComplex.Plus (FilteredObject.Finite.category A)}
    {f : K ⟶ L} {g : L ⟶ M} {S : Realization T K}
    {R : Realization T L} {U : Realization T M} (m : Map f S R) (n : Map g R U) :
    (comp m n).resolutionMap = Resolution.Map.comp m.resolutionMap n.resolutionMap := sorry

/-- The filtered-model component of a composite realization map is the composite. -/
@[simp, stacks 015W "composition of finite filtered right-derived spectral-sequence maps"]
theorem comp_filteredMap {T : A ⥤ₗ B} [EnoughInjectives A]
    {K L M : CochainComplex.Plus (FilteredObject.Finite.category A)}
    {f : K ⟶ L} {g : L ⟶ M} {S : Realization T K}
    {R : Realization T L} {U : Realization T M} (m : Map f S R) (n : Map g R U) :
    (comp m n).filteredMap = m.filteredMap ≫ n.filteredMap := sorry

/-- The spectral-sequence component of a composite realization map is the composite. -/
@[simp, stacks 015W "composition of finite filtered right-derived spectral-sequence maps"]
theorem comp_sequenceMap {T : A ⥤ₗ B} [EnoughInjectives A]
    {K L M : CochainComplex.Plus (FilteredObject.Finite.category A)}
    {f : K ⟶ L} {g : L ⟶ M} {S : Realization T K}
    {R : Realization T L} {U : Realization T M} (m : Map f S R) (n : Map g R U) :
    (comp m n).sequenceMap = m.sequenceMap ≫ n.sequenceMap := sorry

/-- The association component of a composite realization map is the named composite
association morphism. -/
@[simp, stacks 015W "composite association component of finite filtered right-derived maps"]
theorem comp_associationMap {T : A ⥤ₗ B} [EnoughInjectives A]
    {K L M : CochainComplex.Plus (FilteredObject.Finite.category A)}
    {f : K ⟶ L} {g : L ⟶ M} {S : Realization T K}
    {R : Realization T L} {U : Realization T M} (m : Map f S R) (n : Map g R U) :
    (comp m n).associationMap = compAssociationMap m n := sorry

end Realization.Map

end CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence
