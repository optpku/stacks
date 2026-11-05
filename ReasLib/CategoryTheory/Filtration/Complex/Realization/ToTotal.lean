/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.Realization
public import ReasLib.CategoryTheory.Filtration.Complex.SpectralSequence.Association.Total

/-!
# Realization-to-total bridge

The bounded/convergent realization category is an extension of the neutral total category of an
associated spectral sequence.  This file exposes the forgetful bridge without making the neutral
spectral-sequence layer depend on convergence data.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u

namespace CategoryTheory.FilteredComplex.SpectralSequence.Realization

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Forget the boundedness, finiteness, and convergence witnesses of a realization. -/
@[stacks 012C "neutral total object underlying a realization"]
abbrev toTotal (S : Realization (C := C)) :
    FilteredComplex.AssociatedSpectralSequence.Total (C := C) where
  filtered := S.filtered
  sequence := S.sequence
  association := S.association

namespace Map

/-- Send a realization map to the corresponding neutral total morphism. -/
@[stacks 012O "neutral total morphism underlying a realization map"]
abbrev toTotal {S T : Realization (C := C)} (f : Map S T) :
    FilteredComplex.AssociatedSpectralSequence.Total.Hom (toTotal S) (toTotal T) where
  filteredMap := f.filteredMap
  associationMap := f.toAssociationHom

/-- The filtered-complex component is unchanged by the realization-to-total bridge. -/
@[simp, stacks 012O "filtered-complex component of a totalized realization map"]
theorem toTotal_filteredMap {S T : Realization (C := C)} (f : Map S T) :
    (toTotal f).filteredMap = f.filteredMap := sorry

/-- The spectral-sequence component is unchanged by the realization-to-total bridge. -/
@[simp, stacks 012O "spectral-sequence component of a totalized realization map"]
theorem toTotal_sequenceMap {S T : Realization (C := C)} (f : Map S T) :
    (FilteredComplex.AssociatedSpectralSequence.Total.Hom.sequenceMap (toTotal f)) =
      f.sequenceMap := sorry

/-- Recover a realization map from a total morphism between totalized realizations. -/
@[stacks 012O "realization map recovered from a total morphism"]
abbrev ofTotal {S T : Realization (C := C)}
    (f : FilteredComplex.AssociatedSpectralSequence.Total.Hom
      (Realization.toTotal S) (Realization.toTotal T)) : Map S T where
  filteredMap := f.filteredMap
  sequenceMap := FilteredComplex.AssociatedSpectralSequence.Total.Hom.sequenceMap f
  compatible := f.associationMap.compatible

/-- Recovering a realization map preserves its filtered-complex component. -/
@[simp, stacks 012O "filtered-complex component recovered from a total morphism"]
theorem ofTotal_filteredMap {S T : Realization (C := C)}
    (f : FilteredComplex.AssociatedSpectralSequence.Total.Hom
      (Realization.toTotal S) (Realization.toTotal T)) :
    (ofTotal f).filteredMap = f.filteredMap := sorry

/-- Recovering a realization map preserves its spectral-sequence component. -/
@[simp, stacks 012O "spectral-sequence component recovered from a total morphism"]
theorem ofTotal_sequenceMap {S T : Realization (C := C)}
    (f : FilteredComplex.AssociatedSpectralSequence.Total.Hom
      (Realization.toTotal S) (Realization.toTotal T)) :
    (ofTotal f).sequenceMap =
      FilteredComplex.AssociatedSpectralSequence.Total.Hom.sequenceMap f := sorry

/-- Totalizing a recovered realization map returns the original total morphism. -/
@[simp, stacks 012O "totalization after recovering a realization map"]
theorem toTotal_ofTotal {S T : Realization (C := C)}
    (f : FilteredComplex.AssociatedSpectralSequence.Total.Hom
      (Realization.toTotal S) (Realization.toTotal T)) :
    toTotal (ofTotal f) = f := sorry

/-- Recovering a realization map after totalization returns the original map. -/
@[simp, stacks 012O "recovering a realization map after totalization"]
theorem ofTotal_toTotal {S T : Realization (C := C)} (f : Map S T) :
    ofTotal (toTotal f) = f := sorry

/-- Totalization preserves the identity realization map. -/
@[simp, stacks 012O "identity computation for realization totalization"]
theorem toTotal_id (S : Realization (C := C)) :
    toTotal (Realization.Map.id S) =
      FilteredComplex.AssociatedSpectralSequence.Total.Hom.id (Realization.toTotal S) := sorry

/-- Totalization preserves composition of realization maps. -/
@[simp, stacks 012O "composition computation for realization totalization"]
theorem toTotal_comp {S T U : Realization (C := C)} (f : Map S T) (g : Map T U) :
    toTotal (Realization.Map.comp f g) =
      FilteredComplex.AssociatedSpectralSequence.Total.Hom.comp (toTotal f) (toTotal g) := sorry

end Map

/-- The realization-to-total bridge is functorial. -/
@[stacks 012C "functor from realizations to total associated spectral sequences"]
noncomputable def totalFunctor :
    Realization (C := C) ⥤ FilteredComplex.AssociatedSpectralSequence.Total (C := C) where
  obj S := toTotal S
  map f := Map.toTotal f
  map_id := sorry
  map_comp := sorry

/-- The realization-to-total functor is faithful. -/
@[stacks 012C "faithfulness of the realization-to-total functor"]
instance totalFunctor_faithful : (totalFunctor (C := C)).Faithful := sorry

/-- Every total morphism between totalized realizations comes from a realization map. -/
@[stacks 012C "fullness of the realization-to-total functor"]
instance totalFunctor_full : (totalFunctor (C := C)).Full := sorry

/-- The functorial bridge preserves the filtered-complex component of a map. -/
@[simp, stacks 012C "filtered-complex map under the realization-to-total functor"]
theorem totalFunctor_map_filteredMap {S T : Realization (C := C)} (f : S ⟶ T) :
    ((totalFunctor (C := C)).map f).filteredMap = f.filteredMap := sorry

/-- The functorial bridge preserves the spectral-sequence component of a map. -/
@[simp, stacks 012C "spectral-sequence map under the realization-to-total functor"]
theorem totalFunctor_map_sequenceMap {S T : Realization (C := C)} (f : S ⟶ T) :
    FilteredComplex.AssociatedSpectralSequence.Total.Hom.sequenceMap
        ((totalFunctor (C := C)).map f) = f.sequenceMap := sorry

/-- The totalized realization has the same filtered-complex object. -/
@[simp, stacks 012C "filtered-complex object of a totalized realization"]
theorem totalFunctor_obj_filtered (S : Realization (C := C)) :
    ((totalFunctor (C := C)).obj S).filtered = S.filtered := sorry

/-- The totalized realization has the same spectral-sequence object. -/
@[simp, stacks 012C "spectral-sequence object of a totalized realization"]
theorem totalFunctor_obj_sequence (S : Realization (C := C)) :
    ((totalFunctor (C := C)).obj S).sequence = S.sequence := sorry

/-- The totalized realization has the same association data. -/
@[simp, stacks 012C "association data of a totalized realization"]
theorem totalFunctor_obj_association (S : Realization (C := C)) :
    ((totalFunctor (C := C)).obj S).association = S.association := sorry

#synth (totalFunctor (C := C)).Faithful
#synth (totalFunctor (C := C)).Full

end CategoryTheory.FilteredComplex.SpectralSequence.Realization
