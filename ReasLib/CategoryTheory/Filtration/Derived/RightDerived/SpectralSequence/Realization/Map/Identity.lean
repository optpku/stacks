module

public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Realization.Map.Definition
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Identity maps of unbounded filtered right-derived realizations

This file supplies the identity realization map and its filtered, sequence, and association computations.
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

/-- The identity resolution and spectral-sequence maps are compatible with the chosen
association. -/
@[stacks 0BKK "identity map of a filtered right-derived spectral sequence"]
theorem Map.idAssociationCompatible {K : FilteredComplex A} (S : Realization F K) :
    FilteredComplex.Association.IsCompatible S.association S.association
      (modelMap F (KInjectiveResolution.Map.id S.resolution)) (𝟙 S.sequence) := sorry

/-- The association component of the identity map of a right-derived realization. -/
@[stacks 0BKK "identity map of a filtered right-derived spectral sequence"]
noncomputable def Map.idAssociationMap {K : FilteredComplex A} (S : Realization F K) :
    FilteredComplex.Association.Hom S.association S.association
      (modelMap F (KInjectiveResolution.Map.id S.resolution)) where
  hom := 𝟙 S.sequence
  compatible := Map.idAssociationCompatible F S

/-- The identity morphism of a right-derived spectral-sequence realization. -/
@[stacks 0BKK "identity map of a filtered right-derived spectral sequence"]
noncomputable def Map.id {K : FilteredComplex A} (S : Realization F K) :
    Map F (𝟙 K) S S where
  resolutionMap := KInjectiveResolution.Map.id S.resolution
  comparisonCompatible := Model.Comparison.IsCompatible.id F S.comparison
  associationMap := Map.idAssociationMap F S

/-- The resolution component of the identity realization map is the identity resolution map. -/
@[simp, stacks 0BKK "identity map of a filtered right-derived spectral sequence"]
theorem Map.id_resolutionMap {K : FilteredComplex A} (S : Realization F K) :
    (Map.id F S).resolutionMap = KInjectiveResolution.Map.id S.resolution := sorry

/-- The comparison-compatibility component of the identity realization map. -/
@[simp, stacks 0BKK "comparison component of a filtered right-derived identity map"]
theorem Map.id_comparisonCompatible {K : FilteredComplex A} (S : Realization F K) :
    (Map.id F S).comparisonCompatible =
      Model.Comparison.IsCompatible.id F S.comparison := sorry

/-- The association component of the identity realization map is the named identity association
morphism. -/
@[simp, stacks 0BKK "association component of a filtered right-derived identity map"]
theorem Map.id_associationMap {K : FilteredComplex A} (S : Realization F K) :
    (Map.id F S).associationMap = Map.idAssociationMap F S := sorry

/-- The filtered-model component of the identity realization map is the identity. -/
@[simp, stacks 0BKK "identity map of a filtered right-derived spectral sequence"]
theorem Map.id_filteredMap {K : FilteredComplex A} (S : Realization F K) :
    (Map.id F S).filteredMap = 𝟙 S.filtered := sorry

/-- The spectral-sequence component of the identity realization map is the identity. -/
@[simp, stacks 0BKK "identity map of a filtered right-derived spectral sequence"]
theorem Map.id_sequenceMap {K : FilteredComplex A} (S : Realization F K) :
    (Map.id F S).sequenceMap = 𝟙 S.sequence := sorry

/-- The association morphism underlying an identity right-derived realization map is the
canonical association identity, after transporting its dependent filtered-map index. -/
@[simp, stacks 0BKK "identity association morphism of a filtered right-derived realization"]
theorem Map.toAssociationHom_id {K : FilteredComplex A} (S : Realization F K) :
    ((Map.id_filteredMap F S) ▸ (Map.id F S).toAssociationHom) =
      FilteredComplex.Association.Hom.id S.association := sorry

end SpectralSequence.Realization

end CategoryTheory.FilteredComplex.RightDerived
