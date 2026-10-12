/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Realization.Map.Definition
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Composition of unbounded filtered right-derived realization maps

This file composes realization maps and computes all retained components.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape
open Functor.RightDerived.Homotopy

noncomputable section

universe w wA wB vA vB uA uB

namespace CategoryTheory.FilteredComplex.RightDerived

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
variable (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
  [Functor.RightDerived.KInjective.HasDerived F]

namespace SpectralSequence.Realization

/-- Composite resolution and spectral-sequence maps are compatible with the outer chosen
associations. -/
@[stacks 0BKK "composition of maps of filtered right-derived spectral sequences"]
theorem Map.compAssociationCompatible
    {K L M : FilteredComplex A} {f : K ⟶ L} {g : L ⟶ M}
    {S : Realization F K} {T : Realization F L} {U : Realization F M}
    (m : Map F f S T) (n : Map F g T U) :
    FilteredComplex.Association.IsCompatible S.association U.association
      (modelMap F (KInjectiveResolution.Map.comp m.resolutionMap n.resolutionMap))
      (m.sequenceMap ≫ n.sequenceMap) := sorry

/-- The association component of a composite map of right-derived realizations. -/
@[stacks 0BKK "composition of maps of filtered right-derived spectral sequences"]
noncomputable def Map.compAssociationMap
    {K L M : FilteredComplex A} {f : K ⟶ L} {g : L ⟶ M}
    {S : Realization F K} {T : Realization F L} {U : Realization F M}
    (m : Map F f S T) (n : Map F g T U) :
    FilteredComplex.Association.Hom S.association U.association
      (modelMap F (KInjectiveResolution.Map.comp m.resolutionMap n.resolutionMap)) where
  hom := m.sequenceMap ≫ n.sequenceMap
  compatible := Map.compAssociationCompatible F m n

/-- The composite of maps of right-derived spectral-sequence realizations. -/
@[stacks 0BKK "composition of maps of filtered right-derived spectral sequences"]
noncomputable def Map.comp
    {K L M : FilteredComplex A} {f : K ⟶ L} {g : L ⟶ M}
    {S : Realization F K} {T : Realization F L} {U : Realization F M}
    (m : Map F f S T) (n : Map F g T U) : Map F (f ≫ g) S U where
  resolutionMap := KInjectiveResolution.Map.comp m.resolutionMap n.resolutionMap
  comparisonCompatible := Model.Comparison.IsCompatible.comp F
    m.comparisonCompatible n.comparisonCompatible
  associationMap := Map.compAssociationMap F m n

/-- The resolution component of a composite realization map is the composite resolution map. -/
@[simp, stacks 0BKK "composition of maps of filtered right-derived spectral sequences"]
theorem Map.comp_resolutionMap
    {K L M : FilteredComplex A} {f : K ⟶ L} {g : L ⟶ M}
    {S : Realization F K} {T : Realization F L} {U : Realization F M}
    (m : Map F f S T) (n : Map F g T U) :
    (Map.comp F m n).resolutionMap =
      KInjectiveResolution.Map.comp m.resolutionMap n.resolutionMap := sorry

/-- The comparison-compatibility component of a composite realization map is the composite
compatibility proof. -/
@[simp, stacks 0BKK "comparison component of a composite right-derived realization map"]
theorem Map.comp_comparisonCompatible
    {K L M : FilteredComplex A} {f : K ⟶ L} {g : L ⟶ M}
    {S : Realization F K} {T : Realization F L} {U : Realization F M}
    (m : Map F f S T) (n : Map F g T U) :
    (Map.comp F m n).comparisonCompatible =
      Model.Comparison.IsCompatible.comp F
        m.comparisonCompatible n.comparisonCompatible := sorry

/-- The association component of a composite realization map is the named composite association
morphism. -/
@[simp, stacks 0BKK "association component of a composite right-derived realization map"]
theorem Map.comp_associationMap
    {K L M : FilteredComplex A} {f : K ⟶ L} {g : L ⟶ M}
    {S : Realization F K} {T : Realization F L} {U : Realization F M}
    (m : Map F f S T) (n : Map F g T U) :
    (Map.comp F m n).associationMap = Map.compAssociationMap F m n := sorry

/-- The filtered-model component of a composite realization map is the composite model map. -/
@[simp, stacks 0BKK "composition of maps of filtered right-derived spectral sequences"]
theorem Map.comp_filteredMap
    {K L M : FilteredComplex A} {f : K ⟶ L} {g : L ⟶ M}
    {S : Realization F K} {T : Realization F L} {U : Realization F M}
    (m : Map F f S T) (n : Map F g T U) :
    (Map.comp F m n).filteredMap = m.filteredMap ≫ n.filteredMap := sorry

/-- The spectral-sequence component of a composite realization map is the composite map. -/
@[simp, stacks 0BKK "composition of maps of filtered right-derived spectral sequences"]
theorem Map.comp_sequenceMap
    {K L M : FilteredComplex A} {f : K ⟶ L} {g : L ⟶ M}
    {S : Realization F K} {T : Realization F L} {U : Realization F M}
    (m : Map F f S T) (n : Map F g T U) :
    (Map.comp F m n).sequenceMap = m.sequenceMap ≫ n.sequenceMap := sorry

/-- The association morphism underlying a composite right-derived realization map is the
composite association morphism, after transporting its dependent filtered-map index. -/
@[simp, stacks 0BKK "composite association morphism of filtered right-derived realizations"]
theorem Map.toAssociationHom_comp
    {K L M : FilteredComplex A} {f : K ⟶ L} {g : L ⟶ M}
    {S : Realization F K} {T : Realization F L} {U : Realization F M}
    (m : Map F f S T) (n : Map F g T U) :
    ((Map.comp_filteredMap F m n) ▸ (Map.comp F m n).toAssociationHom) =
      FilteredComplex.Association.Hom.comp m.toAssociationHom n.toAssociationHom := sorry

end SpectralSequence.Realization

end CategoryTheory.FilteredComplex.RightDerived
