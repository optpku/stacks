/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Realization.Total
public import ReasLib.CategoryTheory.DisplayedCategory.Total.Transport
public import ReasLib.CategoryTheory.Filtration.Complex.SpectralSequence.Association.Total
public import ReasLib.CategoryTheory.Filtration.Complex.Functors

/-!
# Forgetful functors from total unbounded right-derived realizations

This leaf forgets construction-specific resolution and comparison data while retaining the
associated spectral sequence, its filtered model, its sequence, or its underlying cochain
complex.  All projections read existing realization fields and introduce no new choices.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe wA wB vA vB uA uB

namespace CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Realization

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
variable (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
  [Functor.RightDerived.KInjective.HasDerived F]

namespace Total

/-- The neutral associated-spectral-sequence object underlying a total right-derived
realization. -/
@[stacks 0BKK "associated spectral sequence underlying a total right-derived realization"]
abbrev toAssociated (S : Realization.Total F) :
    FilteredComplex.AssociatedSpectralSequence.Total (C := B) where
  filtered := S.obj.filtered
  sequence := S.obj.sequence
  association := S.obj.association

/-- The neutral associated-spectral-sequence morphism underlying a total realization map. -/
@[stacks 0BKK "associated spectral-sequence map underlying a total realization map"]
abbrev toAssociatedMap {S T : Realization.Total F} (m : S ⟶ T) :
    FilteredComplex.AssociatedSpectralSequence.Total.Hom
      (toAssociated F S) (toAssociated F T) where
  filteredMap := m.displayed.filteredMap
  associationMap := m.displayed.toAssociationHom

/-- Totalization preserves identity maps after forgetting construction-specific data. -/
@[stacks 0BKK "identity computation for associated realization totalization"]
theorem toAssociatedMap_id (S : Realization.Total F) :
    toAssociatedMap F (𝟙 S) =
      FilteredComplex.AssociatedSpectralSequence.Total.Hom.id
        (toAssociated F S) := sorry

/-- Totalization preserves composition after forgetting construction-specific data. -/
@[stacks 0BKK "composition computation for associated realization totalization"]
theorem toAssociatedMap_comp {S T U : Realization.Total F}
    (m : S ⟶ T) (n : T ⟶ U) :
    toAssociatedMap F (m ≫ n) =
      FilteredComplex.AssociatedSpectralSequence.Total.Hom.comp
        (toAssociatedMap F m) (toAssociatedMap F n) := sorry

/-- Reindexing a total realization morphism along an equality of base arrows leaves its associated
spectral-sequence morphism unchanged. -/
@[simp, stacks 0BKK "reindexing computation for associated total realization maps"]
theorem toAssociatedMap_reindex {S T : Realization.Total F}
    {g : S.base ⟶ T.base} (m : S ⟶ T) (h : m.base = g) :
    toAssociatedMap F
        (CategoryTheory.DisplayedCategory.Total.Hom.reindex (f := m) h) =
      toAssociatedMap F m := sorry

/-- Forget total right-derived realizations to neutral associated spectral sequences. -/
@[stacks 0BKK "associated-spectral-sequence functor from total right-derived realizations"]
noncomputable def associatedFunctor :
    Realization.Total F ⥤
      FilteredComplex.AssociatedSpectralSequence.Total (C := B) where
  obj S := toAssociated F S
  map m := toAssociatedMap F m
  map_id := toAssociatedMap_id F
  map_comp := toAssociatedMap_comp F

/-- Forget a total right-derived realization to its filtered model. -/
@[stacks 0BKK "filtered-model projection from total right-derived realizations"]
noncomputable abbrev forgetFiltered :
    Realization.Total F ⥤ FilteredComplex B :=
  associatedFunctor F ⋙
    FilteredComplex.AssociatedSpectralSequence.Total.forgetFiltered

/-- Forget a total right-derived realization to its associated spectral sequence. -/
@[stacks 0BKK "spectral-sequence projection from total right-derived realizations"]
noncomputable abbrev forgetSequence :
    Realization.Total F ⥤ CohomologicalSpectralSequence B 0 :=
  associatedFunctor F ⋙
    FilteredComplex.AssociatedSpectralSequence.Total.forgetSequence

/-- Forget a total right-derived realization to the underlying cochain complex of its filtered
model. -/
@[stacks 0BKK "underlying-complex projection from total right-derived realizations"]
noncomputable abbrev forgetUnderlying :
    Realization.Total F ⥤ CochainComplex B ℤ :=
  forgetFiltered F ⋙ FilteredComplex.underlyingFunctor

/-- The neutral total object retains the filtered model of the realization. -/
@[simp, stacks 0BKK "filtered model of an associated total right-derived realization"]
theorem toAssociated_filtered (S : Realization.Total F) :
    (toAssociated F S).filtered = S.obj.filtered := sorry

/-- The neutral total object retains the spectral sequence of the realization. -/
@[simp, stacks 0BKK "sequence of an associated total right-derived realization"]
theorem toAssociated_sequence (S : Realization.Total F) :
    (toAssociated F S).sequence = S.obj.sequence := sorry

/-- The neutral total object retains the concrete association of the realization. -/
@[simp, stacks 0BKK "association of an associated total right-derived realization"]
theorem toAssociated_association (S : Realization.Total F) :
    (toAssociated F S).association = S.obj.association := sorry

/-- The neutral total map retains the filtered component of a realization map. -/
@[simp, stacks 0BKK "filtered component of an associated total realization map"]
theorem toAssociatedMap_filteredMap {S T : Realization.Total F} (m : S ⟶ T) :
    (toAssociatedMap F m).filteredMap = m.displayed.filteredMap := sorry

/-- The neutral total map retains the spectral-sequence component of a realization map. -/
@[simp, stacks 0BKK "sequence component of an associated total realization map"]
theorem toAssociatedMap_sequenceMap {S T : Realization.Total F} (m : S ⟶ T) :
    FilteredComplex.AssociatedSpectralSequence.Total.Hom.sequenceMap
        (toAssociatedMap F m) = m.displayed.sequenceMap := sorry

/-- The associated-spectral-sequence functor evaluates to the neutral object retained by the
realization. -/
@[simp, stacks 0BKK "object of the associated-spectral-sequence projection"]
theorem associatedFunctor_obj (S : Realization.Total F) :
    (associatedFunctor F).obj S = toAssociated F S := sorry

/-- The associated-spectral-sequence functor maps by the retained neutral morphism. -/
@[simp, stacks 0BKK "map of the associated-spectral-sequence projection"]
theorem associatedFunctor_map {S T : Realization.Total F} (m : S ⟶ T) :
    (associatedFunctor F).map m = toAssociatedMap F m := sorry

/-- The filtered-model projection evaluates to the stored filtered model. -/
@[simp, stacks 0BKK "object of the filtered-model projection"]
theorem forgetFiltered_obj (S : Realization.Total F) :
    (forgetFiltered F).obj S = S.obj.filtered := sorry

/-- The filtered-model projection maps by the filtered component of the realization map. -/
@[simp, stacks 0BKK "map of the filtered-model projection"]
theorem forgetFiltered_map {S T : Realization.Total F} (m : S ⟶ T) :
    (forgetFiltered F).map m = m.displayed.filteredMap := sorry

/-- The spectral-sequence projection evaluates to the stored sequence. -/
@[simp, stacks 0BKK "object of the spectral-sequence projection"]
theorem forgetSequence_obj (S : Realization.Total F) :
    (forgetSequence F).obj S = S.obj.sequence := sorry

/-- The spectral-sequence projection maps by the sequence component of the realization map. -/
@[simp, stacks 0BKK "map of the spectral-sequence projection"]
theorem forgetSequence_map {S T : Realization.Total F} (m : S ⟶ T) :
    (forgetSequence F).map m = m.displayed.sequenceMap := sorry

/-- The underlying-complex projection evaluates to the underlying complex of the filtered
model. -/
@[simp, stacks 0BKK "object of the underlying-complex projection"]
theorem forgetUnderlying_obj (S : Realization.Total F) :
    (forgetUnderlying F).obj S = S.obj.filtered.underlying := sorry

/-- The underlying-complex projection maps by the underlying map of the filtered component. -/
@[simp, stacks 0BKK "map of the underlying-complex projection"]
theorem forgetUnderlying_map {S T : Realization.Total F} (m : S ⟶ T) :
    (forgetUnderlying F).map m =
      FilteredComplex.underlyingMap m.displayed.filteredMap := sorry

end Total

end CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Realization
