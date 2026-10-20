/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.SpectralSequence.AssociationMorphism

/-!
# Total category of associated spectral sequences

This file owns the neutral categorical layer for a filtered complex together with a chosen
associated cohomological spectral sequence.  Boundedness, finiteness, convergence, and application
specific page identifications belong to extensions such as `Realization`.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace FilteredComplex.AssociatedSpectralSequence

/-- A filtered complex together with chosen association data for a spectral sequence. -/
@[stacks 012M "total object of an associated spectral sequence"]
structure Total where
  /-- The filtered complex underlying the chosen association. -/
  filtered : FilteredComplex C
  /-- The selected cohomological spectral sequence. -/
  sequence : CohomologicalSpectralSequence C 0
  /-- Concrete association data for the selected spectral sequence. -/
  association : FilteredComplex.Association filtered sequence

namespace Total

/-- A morphism of total associated-spectral-sequence objects consists of a filtered-complex map
and its compatible, uniquely determined spectral-sequence map. -/
@[stacks 012O "morphism of total associated spectral sequences"]
structure Hom (S T : Total (C := C)) where
  /-- The underlying filtered-complex morphism. -/
  filteredMap : S.filtered ⟶ T.filtered
  /-- The compatible morphism of the chosen associated spectral sequences. -/
  associationMap :
    FilteredComplex.Association.Hom S.association T.association filteredMap

namespace Hom

/-- The spectral-sequence component of a total morphism. -/
@[stacks 012O "spectral sequence component of a total morphism"]
abbrev sequenceMap {S T : Total (C := C)} (f : Hom S T) : S.sequence ⟶ T.sequence :=
  f.associationMap.hom

/-- The identity morphism of a total associated-spectral-sequence object. -/
@[stacks 012O "identity morphism of total associated spectral sequences"]
noncomputable def id (S : Total (C := C)) : Hom S S where
  filteredMap := 𝟙 S.filtered
  associationMap := FilteredComplex.Association.Hom.id S.association

/-- The composite of two total associated-spectral-sequence morphisms. -/
@[stacks 012O "composition of total associated spectral-sequence morphisms"]
noncomputable def comp {S T U : Total (C := C)} (f : Hom S T) (g : Hom T U) : Hom S U where
  filteredMap := f.filteredMap ≫ g.filteredMap
  associationMap := FilteredComplex.Association.Hom.comp f.associationMap g.associationMap

/-- Total morphisms are determined by their filtered-complex component. -/
@[ext, stacks 012O "extensionality of total associated spectral-sequence morphisms"]
theorem ext {S T : Total (C := C)} {f g : Hom S T}
    (h : f.filteredMap = g.filteredMap) : f = g := sorry

/-- The filtered-complex component of the identity total morphism. -/
@[simp, stacks 012O "identity filtered-complex component of a total morphism"]
theorem id_filteredMap (S : Total (C := C)) :
    (id S).filteredMap = 𝟙 S.filtered := sorry

/-- The spectral-sequence component of the identity total morphism. -/
@[simp, stacks 012O "identity spectral-sequence component of a total morphism"]
theorem id_sequenceMap (S : Total (C := C)) :
    Hom.sequenceMap (id S) = 𝟙 S.sequence := sorry

/-- The filtered-complex component of a composite total morphism. -/
@[simp, reassoc, stacks 012O "composition filtered-complex component of a total morphism"]
theorem comp_filteredMap {S T U : Total (C := C)} (f : Hom S T) (g : Hom T U) :
    (comp f g).filteredMap = f.filteredMap ≫ g.filteredMap := sorry

/-- The spectral-sequence component of a composite total morphism. -/
@[simp, reassoc, stacks 012O "composition spectral-sequence component of a total morphism"]
theorem comp_sequenceMap {S T U : Total (C := C)} (f : Hom S T) (g : Hom T U) :
    Hom.sequenceMap (comp f g) = Hom.sequenceMap f ≫ Hom.sequenceMap g := sorry

/-- The stored association morphism of a total morphism. -/
@[simp, stacks 012O "association morphism of a total morphism"]
abbrev toAssociationHom {S T : Total (C := C)} (f : Hom S T) :
    FilteredComplex.Association.Hom S.association T.association f.filteredMap :=
  f.associationMap

/-- The spectral-sequence component of the association morphism stored in a total map. -/
@[simp, stacks 012O "spectral-sequence projection of a total association morphism"]
theorem toAssociationHom_hom {S T : Total (C := C)} (f : Hom S T) :
    f.toAssociationHom.hom = Hom.sequenceMap f := sorry

/-- The compatibility proof stored in a total map is the compatibility proof of its association
morphism. -/
@[stacks 012O "compatibility projection of a total association morphism"]
theorem toAssociationHom_compatible {S T : Total (C := C)} (f : Hom S T) :
    f.toAssociationHom.compatible = f.associationMap.compatible := sorry

/-- The association morphism attached to the identity total map. -/
@[simp, stacks 012O "identity association morphism of a total map"]
theorem toAssociationHom_id (S : Total (C := C)) :
    (id S).toAssociationHom = FilteredComplex.Association.Hom.id S.association := sorry

/-- The association morphism attached to a composite total map. -/
@[simp, stacks 012O "composition association morphism of a total map"]
theorem toAssociationHom_comp {S T U : Total (C := C)} (f : Hom S T) (g : Hom T U) :
    (comp f g).toAssociationHom =
      FilteredComplex.Association.Hom.comp f.toAssociationHom g.toAssociationHom := sorry

end Hom

/-- The category of total associated-spectral-sequence objects. -/
@[stacks 012M "category of total associated spectral sequences"]
noncomputable instance : Category (Total (C := C)) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  assoc := sorry
  id_comp := sorry
  comp_id := sorry

/-- Forget a total object to its filtered complex. -/
@[stacks 012M "filtered-complex forgetful functor for total associated objects"]
noncomputable def forgetFiltered : Total (C := C) ⥤ FilteredComplex C where
  obj S := S.filtered
  map f := f.filteredMap
  map_id := sorry
  map_comp := sorry

/-- Forget a total object to its chosen spectral sequence. -/
@[stacks 012M "spectral-sequence forgetful functor for total associated objects"]
noncomputable def forgetSequence : Total (C := C) ⥤ CohomologicalSpectralSequence C 0 where
  obj S := S.sequence
  map f := Hom.sequenceMap f
  map_id := sorry
  map_comp := sorry

/-- The filtered-complex forgetful functor is faithful because compatible spectral-sequence maps
are unique over a fixed filtered-complex map. -/
@[stacks 012M "faithful filtered-complex forgetful functor for total associated objects"]
instance forgetFiltered_faithful : (forgetFiltered (C := C)).Faithful := sorry

/-- Equality of total morphisms can be checked after forgetting to filtered complexes. -/
@[stacks 012M "equality criterion for total associated morphisms"]
theorem forgetFiltered_map_eq_iff {S T : Total (C := C)} (f g : S ⟶ T) :
    (forgetFiltered (C := C)).map f = (forgetFiltered (C := C)).map g ↔ f = g := sorry

/-- The filtered-complex object underlying a total object. -/
@[simp, stacks 012M "filtered-complex object of a total associated object"]
theorem forgetFiltered_obj (S : Total (C := C)) :
    (forgetFiltered (C := C)).obj S = S.filtered := sorry

/-- The filtered-complex map underlying a total morphism. -/
@[simp, stacks 012M "filtered-complex map of a total associated morphism"]
theorem forgetFiltered_map {S T : Total (C := C)} (f : S ⟶ T) :
    (forgetFiltered (C := C)).map f = f.filteredMap := sorry

/-- The spectral-sequence object underlying a total object. -/
@[simp, stacks 012M "spectral-sequence object of a total associated object"]
theorem forgetSequence_obj (S : Total (C := C)) :
    (forgetSequence (C := C)).obj S = S.sequence := sorry

/-- The spectral-sequence map underlying a total morphism. -/
@[simp, stacks 012M "spectral-sequence map of a total associated morphism"]
theorem forgetSequence_map {S T : Total (C := C)} (f : S ⟶ T) :
    (forgetSequence (C := C)).map f =
      Hom.sequenceMap f := sorry

#synth (forgetFiltered (C := C)).Faithful

end Total

end CategoryTheory.FilteredComplex.AssociatedSpectralSequence
