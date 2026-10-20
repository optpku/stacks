/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Truncation.Naturality.Displayed
public import ReasLib.CategoryTheory.DisplayedCategory.Total.Transport
public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Realization.Total.Forget
public import ReasLib.CategoryTheory.Filtration.Complex.SpectralSequence.Association.Total
public import ReasLib.CategoryTheory.Filtration.Complex.Functors
public import ReasLib.CategoryTheory.Homology.SpectralSequence.Renumber.FromZero
import Mathlib.Tactic.CrossRefAttribute

/-!
# Total and neutral views of truncation realizations

The selected representative of a derived object is not functorial on the derived category alone.
A morphism in the total realization category does retain a representative lift, so the selected
truncation filtration and the generic realization are functorial on that total category.  This
leaf packages that functor together with the filtered, sequence, and underlying projections.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w wA wB vA vB uA uB

namespace CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Truncation

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]

namespace Realization

variable (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
  [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A]

/-! The total category and its dependent generic realization views. -/

/-- The total category of truncation-filtration realizations over the derived base. -/
@[stacks 0BKM "total category of truncation-filtration realizations"]
abbrev Total := DisplayedCategory.Total (displayedCategory F)

namespace Total

/-- Forget a total truncation realization to its derived-category base object. -/
@[stacks 0BKM "derived base of a total truncation realization"]
abbrev forgetBase : Total F ⥤ DerivedCategory A :=
  DisplayedCategory.Total.forget (displayedCategory F)

/-- The base object of the total truncation realization is its selected derived object. -/
@[simp, stacks 0BKM "base object of a total truncation realization"]
theorem forgetBase_obj (S : Total F) :
    (forgetBase F).obj S = S.base := sorry

/-- The base map of a total truncation realization morphism is its derived morphism. -/
@[simp, stacks 0BKM "base map of a total truncation realization"]
theorem forgetBase_map {S T : Total F} (m : S ⟶ T) :
    (forgetBase F).map m = m.base := sorry

/-- Two total truncation morphisms are equal when their base maps agree and their displayed maps
agree after owner-level reindexing. -/
@[ext (iff := false), stacks 0BKM "extensionality of total truncation realization maps"]
theorem Hom.ext_reindex {S T : Total F} {m n : S ⟶ T}
    (h_base : m.base = n.base)
    (h_map : Realization.Map.reindex F h_base m.displayed = n.displayed) :
    m = n := sorry

/-- The generic realization retained by a total truncation realization.

The target filtered complex depends on the selected representative of `S.base`; this is why the
view is a dependent term rather than a functor on the derived category. -/
@[stacks 0BKM "generic realization retained by a total truncation realization"]
noncomputable abbrev toGeneric (S : Total F) :
    RightDerived.SpectralSequence.Realization F
      (DerivedCategory.truncationFilteredPreimage S.base) :=
  S.obj.original

/-- The generic realization map retained by a total truncation-realization morphism. -/
@[stacks 0BKM "generic map retained by a total truncation realization"]
noncomputable abbrev toGenericMap {S T : Total F} (m : S ⟶ T) :
    RightDerived.SpectralSequence.Realization.Map F
      (CochainComplex.TruncationFiltration.map m.displayed.lift.hom)
      (toGeneric F S) (toGeneric F T) :=
  m.displayed.original

/-- The functor from total truncation realizations to total generic filtered realizations.

Its base map is induced by the selected lift carried by the truncation-realization morphism. -/
@[stacks 0BKM "generic realization functor from total truncation realizations"]
noncomputable def genericFunctor :
    Total F ⥤ RightDerived.SpectralSequence.Realization.Total F where
  obj S :=
    { base := DerivedCategory.truncationFilteredPreimage S.base
      obj := S.obj.original }
  map m :=
    { base := CochainComplex.TruncationFiltration.map m.displayed.lift.hom
      displayed := m.displayed.original }
  map_id := sorry
  map_comp := sorry

/-- The generic functor sends a total truncation object to the truncation filtration of its
selected representative. -/
@[simp, stacks 0BKM "base object of the truncation-to-generic functor"]
theorem genericFunctor_obj_base (S : Total F) :
    ((genericFunctor F).obj S).base =
      DerivedCategory.truncationFilteredPreimage S.base := sorry

/-- The displayed object of the generic functor is the retained generic realization. -/
@[simp, stacks 0BKM "displayed object of the truncation-to-generic functor"]
theorem genericFunctor_obj_displayed (S : Total F) :
    ((genericFunctor F).obj S).obj = toGeneric F S := sorry

/-- The base map of the generic functor is induced by the selected representative lift. -/
@[simp, stacks 0BKM "base map of the truncation-to-generic functor"]
theorem genericFunctor_map_base {S T : Total F} (m : S ⟶ T) :
    ((genericFunctor F).map m).base =
      CochainComplex.TruncationFiltration.map m.displayed.lift.hom := sorry

/-- The displayed map of the generic functor is the retained generic realization map. -/
@[simp, stacks 0BKM "displayed map of the truncation-to-generic functor"]
theorem genericFunctor_map_displayed {S T : Total F} (m : S ⟶ T) :
    ((genericFunctor F).map m).displayed = toGenericMap F m := sorry

/-- The truncation-to-generic total functor is faithful: its filtered base map recovers the
selected lift, and its displayed component recovers the realization map. -/
@[stacks 0BKM "faithfulness of the truncation-to-generic realization functor"]
noncomputable instance genericFunctor_faithful :
    (genericFunctor F).Faithful := sorry

/-- Forget a total truncation realization to the truncation filtration of its selected
representative. -/
@[stacks 0BKM "selected filtered-preimage projection from total truncation realizations"]
noncomputable abbrev forgetPreimage : Total F ⥤ FilteredComplex A :=
  genericFunctor F ⋙ RightDerived.SpectralSequence.Realization.Total.forgetBase F

/-- The selected filtered-preimage projection evaluates to the canonical truncation filtration. -/
@[simp, stacks 0BKM "selected filtered preimage of a total truncation realization"]
theorem forgetPreimage_obj (S : Total F) :
    (forgetPreimage F).obj S =
      DerivedCategory.truncationFilteredPreimage S.base := sorry

/-- The selected filtered-preimage projection maps by the retained lift. -/
@[simp, stacks 0BKM "selected filtered-preimage map of a total truncation realization"]
theorem forgetPreimage_map {S T : Total F} (m : S ⟶ T) :
    (forgetPreimage F).map m =
      CochainComplex.TruncationFiltration.map m.displayed.lift.hom := sorry

/-- The filtered component of the dependent generic map. -/
@[simp, stacks 0BKM "filtered component of a retained truncation generic map"]
theorem toGenericMap_filteredMap {S T : Total F} (m : S ⟶ T) :
    (toGenericMap F m).filteredMap = m.displayed.filteredMap := sorry

/-- The original spectral-sequence component of the dependent generic map. -/
@[simp, stacks 0BKM "sequence component of a retained truncation generic map"]
theorem toGenericMap_sequenceMap {S T : Total F} (m : S ⟶ T) :
    (toGenericMap F m).sequenceMap = m.displayed.original.sequenceMap := sorry

/-- The filtered-model projection from total truncation realizations. -/
@[stacks 0BKM "filtered-model projection from total truncation realizations"]
noncomputable def forgetFiltered : Total F ⥤ FilteredComplex B where
  obj S := S.obj.filtered
  map m := m.displayed.filteredMap
  map_id := sorry
  map_comp := sorry

/-- The original, zero-based spectral-sequence projection from total truncation realizations. -/
@[stacks 0BKM "original spectral-sequence projection from total truncation realizations"]
noncomputable def forgetOriginalSequence :
    Total F ⥤ CohomologicalSpectralSequence B 0 where
  obj S := S.obj.originalSequence
  map m := m.displayed.original.sequenceMap
  map_id := sorry
  map_comp := sorry

/-- The standard page-two-renumbered spectral-sequence projection. -/
@[stacks 0BKM "renumbered spectral-sequence projection from total truncation realizations"]
noncomputable def forgetSequence :
    Total F ⥤ E₂CohomologicalSpectralSequence B where
  obj S := S.obj.sequence
  map m := m.displayed.sequenceMap
  map_id := sorry
  map_comp := sorry

/-- The underlying cochain-complex projection of total truncation realizations. -/
@[stacks 0BKM "underlying-complex projection from total truncation realizations"]
noncomputable def forgetUnderlying : Total F ⥤ CochainComplex B ℤ :=
  forgetFiltered F ⋙ FilteredComplex.underlyingFunctor

/-- The filtered object retained by the filtered-model projection. -/
@[simp, stacks 0BKM "filtered model of a total truncation realization"]
theorem forgetFiltered_obj (S : Total F) :
    (forgetFiltered F).obj S = S.obj.filtered := sorry

/-- The filtered map retained by the filtered-model projection. -/
@[simp, stacks 0BKM "filtered map of a total truncation realization"]
theorem forgetFiltered_map {S T : Total F} (m : S ⟶ T) :
    (forgetFiltered F).map m = m.displayed.filteredMap := sorry

/-- The original sequence retained by the zero-based projection. -/
@[simp, stacks 0BKM "original sequence of a total truncation realization"]
theorem forgetOriginalSequence_obj (S : Total F) :
    (forgetOriginalSequence F).obj S = S.obj.originalSequence := sorry

/-- The original sequence map retained by the zero-based projection. -/
@[simp, stacks 0BKM "original sequence map of a total truncation realization"]
theorem forgetOriginalSequence_map {S T : Total F} (m : S ⟶ T) :
    (forgetOriginalSequence F).map m = m.displayed.original.sequenceMap := sorry

/-- The renumbered sequence retained by the page-two projection. -/
@[simp, stacks 0BKM "renumbered sequence of a total truncation realization"]
theorem forgetSequence_obj (S : Total F) :
    (forgetSequence F).obj S = S.obj.sequence := sorry

/-- The renumbered sequence map retained by the page-two projection. -/
@[simp, stacks 0BKM "renumbered sequence map of a total truncation realization"]
theorem forgetSequence_map {S T : Total F} (m : S ⟶ T) :
    (forgetSequence F).map m = m.displayed.sequenceMap := sorry

/-- The underlying cochain complex retained by a total truncation realization. -/
@[simp, stacks 0BKM "underlying complex of a total truncation realization"]
theorem forgetUnderlying_obj (S : Total F) :
    (forgetUnderlying F).obj S = S.obj.filtered.underlying := sorry

/-- The underlying cochain map retained by a total truncation realization. -/
@[simp, stacks 0BKM "underlying map of a total truncation realization"]
theorem forgetUnderlying_map {S T : Total F} (m : S ⟶ T) :
    (forgetUnderlying F).map m = FilteredComplex.underlyingMap m.displayed.filteredMap := sorry

/-- The neutral associated-spectral-sequence object retained by a total truncation realization. -/
@[stacks 0BKM "neutral associated object of a total truncation realization"]
noncomputable def toAssociated (S : Total F) :
    FilteredComplex.AssociatedSpectralSequence.Total (C := B) where
  filtered := S.obj.filtered
  sequence := S.obj.originalSequence
  association := S.obj.association

/-- The neutral associated-spectral-sequence morphism retained by a total truncation map. -/
@[stacks 0BKM "neutral associated map of a total truncation realization"]
noncomputable def toAssociatedMap {S T : Total F} (m : S ⟶ T) :
    FilteredComplex.AssociatedSpectralSequence.Total.Hom
      (toAssociated F S) (toAssociated F T) where
  filteredMap := m.displayed.filteredMap
  associationMap := m.displayed.toAssociationHom

/-- Totalization of a truncation identity retains the neutral identity map. -/
@[stacks 0BKM "identity law for neutral truncation associated maps"]
theorem toAssociatedMap_id (S : Total F) :
    toAssociatedMap F (𝟙 S) =
      FilteredComplex.AssociatedSpectralSequence.Total.Hom.id (toAssociated F S) := sorry

/-- Totalization of a truncation composite retains the neutral composite map. -/
@[stacks 0BKM "composition law for neutral truncation associated maps"]
theorem toAssociatedMap_comp {S T U : Total F} (m : S ⟶ T) (n : T ⟶ U) :
    toAssociatedMap F (m ≫ n) =
      FilteredComplex.AssociatedSpectralSequence.Total.Hom.comp
        (toAssociatedMap F m) (toAssociatedMap F n) := sorry

/-- Reindexing a total truncation morphism along an equality of base arrows leaves its associated
spectral-sequence morphism unchanged. -/
@[simp, stacks 0BKM "reindexing computation for neutral truncation associated maps"]
theorem toAssociatedMap_reindex {S T : Total F}
    {g : S.base ⟶ T.base} (m : S ⟶ T) (h : m.base = g) :
    toAssociatedMap F
        (CategoryTheory.DisplayedCategory.Total.Hom.reindex (f := m) h) =
      toAssociatedMap F m := sorry

/-- The neutral truncation associated map retains the filtered component of the total map. -/
@[simp, stacks 0BKM "filtered component of a neutral truncation associated map"]
theorem toAssociatedMap_filteredMap {S T : Total F} (m : S ⟶ T) :
    (toAssociatedMap F m).filteredMap = m.displayed.filteredMap := sorry

/-- The neutral truncation associated map retains the unrenumbered spectral-sequence component. -/
@[simp, stacks 0BKM "sequence component of a neutral truncation associated map"]
theorem toAssociatedMap_sequenceMap {S T : Total F} (m : S ⟶ T) :
    FilteredComplex.AssociatedSpectralSequence.Total.Hom.sequenceMap
        (toAssociatedMap F m) = m.displayed.original.sequenceMap := sorry

/-- The functor from total truncation realizations to neutral associated data. -/
@[stacks 0BKM "associated-spectral-sequence functor for total truncation realizations"]
noncomputable def associatedFunctor :
    Total F ⥤ FilteredComplex.AssociatedSpectralSequence.Total (C := B) where
  obj := toAssociated F
  map := toAssociatedMap F
  map_id := toAssociatedMap_id F
  map_comp := toAssociatedMap_comp F

/-- The associated functor evaluates to the neutral object retained by the realization. -/
@[simp, stacks 0BKM "object computation for the truncation associated functor"]
theorem associatedFunctor_obj (S : Total F) :
    (associatedFunctor F).obj S = toAssociated F S := sorry

/-- The associated functor maps by the neutral map retained by the realization. -/
@[simp, stacks 0BKM "map computation for the truncation associated functor"]
theorem associatedFunctor_map {S T : Total F} (m : S ⟶ T) :
    (associatedFunctor F).map m = toAssociatedMap F m := sorry

end Total

end Realization

end CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Truncation
