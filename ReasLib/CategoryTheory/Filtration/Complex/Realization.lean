/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.Convergence
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Realizations of Filtered Spectral Sequences

This file owns the common concrete data of a bounded convergent cohomological spectral sequence
associated to a filtered complex. Derived-functor and double-complex applications add their page
and abutment identifications in their own modules.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u

namespace CategoryTheory.FilteredComplex.SpectralSequence

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A chosen bounded, convergent cohomological spectral sequence associated to a filtered
complex. The page formulas and abutment comparisons belong to specialized extensions. -/
@[stacks 012C "filtered spectral-sequence realization"]
structure Realization where
  /-- The filtered complex underlying the realization. -/
  filtered : FilteredComplex C
  /-- The cohomological spectral sequence associated to `filtered`. -/
  sequence : CohomologicalSpectralSequence C 0
  /-- Concrete association data between `filtered` and `sequence`. -/
  association : FilteredComplex.Association filtered sequence
  /-- The spectral sequence is bounded. -/
  bounded : sequence.IsBounded
  /-- The induced filtrations on the cohomology of `filtered` are finite. -/
  finite : FilteredComplex.Cohomology.Filtration.IsFinite filtered
  /-- The spectral sequence converges to the cohomology of `filtered`. -/
  converges : FilteredComplex.Cohomology.Convergence.Converges filtered sequence

/-- A chosen realization supplies the canonical existential association predicate. -/
@[stacks 012C "filtered spectral-sequence association"]
theorem Realization.isAssociated (S : Realization (C := C)) :
    FilteredComplex.IsAssociated S.filtered S.sequence := sorry

namespace Realization

/-- A morphism between chosen filtered spectral-sequence realizations. Specialized realization
maps extend this owner with their page and abutment naturality data. -/
@[stacks 012C "filtered spectral-sequence realization map"]
structure Map (S T : Realization (C := C)) where
  /-- The underlying morphism of filtered complexes. -/
  filteredMap : S.filtered ⟶ T.filtered
  /-- The induced morphism of cohomological spectral sequences. -/
  sequenceMap : S.sequence ⟶ T.sequence
  /-- The spectral-sequence morphism is compatible with the filtered-complex morphism. -/
  compatible : FilteredComplex.Association.IsCompatible
    S.association T.association filteredMap sequenceMap

namespace Map

/-- Two realization maps are equal when their filtered-complex and spectral-sequence components
agree; the inducedness condition is proposition-valued. -/
@[ext, stacks 012O "extensionality of induced filtered spectral-sequence maps"]
theorem ext {S T : Realization (C := C)} {f g : Realization.Map S T}
    (h_filtered : f.filteredMap = g.filteredMap)
    (h_sequence : f.sequenceMap = g.sequenceMap) : f = g := sorry

/-- An association-induced realization map is determined by its filtered-complex component.
Indeed, the associated spectral-sequence map is unique once that component is fixed. -/
@[stacks 012O "extensionality of induced filtered spectral-sequence maps"]
theorem ext_filteredMap {S T : Realization (C := C)} {f g : Realization.Map S T}
    (h_filtered : f.filteredMap = g.filteredMap) : f = g := sorry

/-- The identity morphism of a chosen filtered spectral-sequence realization. -/
@[stacks 012C "identity filtered spectral-sequence realization map"]
noncomputable def id (S : Realization (C := C)) : Map S S where
  filteredMap := 𝟙 S.filtered
  sequenceMap := 𝟙 S.sequence
  compatible := FilteredComplex.Association.IsCompatible.id S.association

/-- The filtered-complex component of the identity realization map is the identity. -/
@[simp, stacks 012C "identity filtered spectral-sequence realization map"]
theorem id_filteredMap (S : Realization (C := C)) :
    (id S).filteredMap = 𝟙 S.filtered := sorry

/-- The spectral-sequence component of the identity realization map is the identity. -/
@[simp, stacks 012C "identity filtered spectral-sequence realization map"]
theorem id_sequenceMap (S : Realization (C := C)) :
    (id S).sequenceMap = 𝟙 S.sequence := sorry

/-- The composite of two chosen filtered spectral-sequence realization maps. -/
@[stacks 012C "composition of filtered spectral-sequence realization maps"]
noncomputable def comp {S T U : Realization (C := C)}
    (f : Map S T) (g : Map T U) : Map S U where
  filteredMap := f.filteredMap ≫ g.filteredMap
  sequenceMap := f.sequenceMap ≫ g.sequenceMap
  compatible := FilteredComplex.Association.IsCompatible.comp
    S.association T.association U.association f.compatible g.compatible

/-- The filtered-complex component of a composite realization map is the composite map. -/
@[simp, stacks 012C "composition of filtered spectral-sequence realization maps"]
theorem comp_filteredMap {S T U : Realization (C := C)}
    (f : Map S T) (g : Map T U) :
    (comp f g).filteredMap = f.filteredMap ≫ g.filteredMap := sorry

/-- The spectral-sequence component of a composite realization map is the composite map. -/
@[simp, stacks 012C "composition of filtered spectral-sequence realization maps"]
theorem comp_sequenceMap {S T U : Realization (C := C)}
    (f : Map S T) (g : Map T U) :
    (comp f g).sequenceMap = f.sequenceMap ≫ g.sequenceMap := sorry

/-- A realization map supplies an explicitly compatible morphism between its underlying
associated spectral sequences. -/
@[stacks 012O "underlying morphism of associated spectral sequences"]
def toAssociationHom {S T : Realization (C := C)} (f : Map S T) :
    FilteredComplex.Association.Hom S.association T.association f.filteredMap where
  hom := f.sequenceMap
  compatible := f.compatible

/-- The association morphism attached to a realization map has the same spectral-sequence
component as the original map. -/
@[simp, stacks 012O "spectral-sequence component of an association morphism"]
theorem toAssociationHom_hom {S T : Realization (C := C)} (f : Map S T) :
    f.toAssociationHom.hom = f.sequenceMap := sorry

/-- The association morphism attached to the identity realization map is the canonical
association identity. -/
@[simp, stacks 012O "identity computation for an association morphism"]
theorem toAssociationHom_id (S : Realization (C := C)) :
    (id S).toAssociationHom = FilteredComplex.Association.Hom.id S.association := sorry

/-- The association morphism attached to a composite realization map is the composite of the
associated morphisms. -/
@[simp, stacks 012O "composition computation for an association morphism"]
theorem toAssociationHom_comp {S T U : Realization (C := C)}
    (f : Map S T) (g : Map T U) :
    (comp f g).toAssociationHom =
      FilteredComplex.Association.Hom.comp f.toAssociationHom g.toAssociationHom := sorry

/-- The first-page comparison carried by a generic realization is natural for a realization
map. This facade keeps downstream code at the realization layer. -/
@[reassoc, stacks 012O "naturality of a filtered realization first-page map"]
theorem pageOne_naturality {S T : Realization (C := C)} (f : Map S T) (p q : ℤ) :
    (f.sequenceMap.hom 1).f (p, q) ≫ (T.association.pageOneIso p q).hom =
      (S.association.pageOneIso p q).hom ≫
        HomologicalComplex.homologyMap
          (FilteredComplex.gradedPieceMap f.filteredMap p) (p + q) := sorry

/-- The inverse first-page comparison of a generic realization map is natural with respect to
the induced map on graded-piece homology. -/
@[reassoc, stacks 012O "inverse naturality of a filtered realization first-page map"]
theorem pageOne_inv_naturality {S T : Realization (C := C)}
    (f : Map S T) (p q : ℤ) :
    HomologicalComplex.homologyMap
          (FilteredComplex.gradedPieceMap f.filteredMap p) (p + q) ≫
        (T.association.pageOneIso p q).inv =
      (S.association.pageOneIso p q).inv ≫
        (f.sequenceMap.hom 1).f (p, q) := sorry

/-- Conjugating the graded-piece homology map by the chosen first-page comparisons recovers the
page component of a generic realization map. -/
@[reassoc, stacks 012O "computation of a filtered realization first-page map"]
theorem pageOne_naturality_inv {S T : Realization (C := C)}
    (f : Map S T) (p q : ℤ) :
    (S.association.pageOneIso p q).hom ≫
        HomologicalComplex.homologyMap
          (FilteredComplex.gradedPieceMap f.filteredMap p) (p + q) ≫
        (T.association.pageOneIso p q).inv =
      (f.sequenceMap.hom 1).f (p, q) := sorry

/-- Conjugating the page component by the inverse first-page comparisons recovers the map on
graded-piece homology. -/
@[reassoc, stacks 012O "target-map computation of a filtered realization first-page map"]
theorem pageOne_target_map {S T : Realization (C := C)}
    (f : Map S T) (p q : ℤ) :
    (S.association.pageOneIso p q).inv ≫
        (f.sequenceMap.hom 1).f (p, q) ≫
      (T.association.pageOneIso p q).hom =
      HomologicalComplex.homologyMap
        (FilteredComplex.gradedPieceMap f.filteredMap p) (p + q) := sorry

end Map

/-- Chosen filtered spectral-sequence realizations and association-preserving maps form a
category.  This lets applications use the ordinary categorical interface while retaining the
filtered-complex and spectral-sequence components of every morphism. -/
@[stacks 012C "category of filtered spectral-sequence realizations"]
noncomputable instance : Category (Realization (C := C)) where
  Hom S T := Map S T
  id S := Map.id S
  comp f g := Map.comp f g
  assoc := sorry
  id_comp := sorry
  comp_id := sorry

/-- The functor forgetting a filtered spectral-sequence realization to its filtered complex. -/
@[stacks 012C "forgetful functor from filtered spectral-sequence realizations"]
noncomputable def forgetFiltered : Realization (C := C) ⥤ FilteredComplex C where
  obj S := S.filtered
  map f := f.filteredMap
  map_id := sorry
  map_comp := sorry

/-- The functor forgetting a filtered spectral-sequence realization to its spectral sequence. -/
@[stacks 012C "forgetful functor from filtered spectral-sequence realizations"]
noncomputable def forgetSequence :
    Realization (C := C) ⥤ CohomologicalSpectralSequence C 0 where
  obj S := S.sequence
  map f := f.sequenceMap
  map_id := sorry
  map_comp := sorry

/-- The filtered-complex object underlying a realization is the value of `forgetFiltered`. -/
@[simp, stacks 012C "forgetful functor from filtered spectral-sequence realizations"]
theorem forgetFiltered_obj (S : Realization (C := C)) :
    (forgetFiltered (C := C)).obj S = S.filtered := sorry

/-- The image under `forgetFiltered` of a realization map is its filtered-complex component. -/
@[simp, stacks 012C "forgetful functor from filtered spectral-sequence realizations"]
theorem forgetFiltered_map {S T : Realization (C := C)} (f : S ⟶ T) :
    (forgetFiltered (C := C)).map f = f.filteredMap := sorry

/-- The filtered-complex forgetful functor maps an identity to an identity. -/
@[simp, stacks 012C "identity computation for the filtered-complex forgetful functor"]
theorem forgetFiltered_map_id (S : Realization (C := C)) :
    (forgetFiltered (C := C)).map (𝟙 S) = 𝟙 S.filtered := sorry

/-- The filtered-complex forgetful functor preserves composition. -/
@[simp, reassoc, stacks 012C "composition computation for the filtered-complex forgetful functor"]
theorem forgetFiltered_map_comp
    {S T U : Realization (C := C)} (f : S ⟶ T) (g : T ⟶ U) :
    (forgetFiltered (C := C)).map (f ≫ g) =
      (forgetFiltered (C := C)).map f ≫ (forgetFiltered (C := C)).map g := sorry

/-- Forgetting a chosen realization to its filtered complex is faithful: association-induced
spectral-sequence maps are determined by their filtered-complex component. -/
@[stacks 012C "faithful forgetful functor from filtered spectral-sequence realizations"]
instance forgetFiltered_faithful : (forgetFiltered (C := C)).Faithful := sorry

/-- Equality of realization maps can be checked after forgetting to filtered complexes. -/
@[stacks 012C "equality criterion via the filtered-complex forgetful functor"]
theorem forgetFiltered_map_eq_iff {S T : Realization (C := C)} (f g : S ⟶ T) :
    (forgetFiltered (C := C)).map f = (forgetFiltered (C := C)).map g ↔ f = g := sorry

/-- An isomorphism of underlying filtered complexes induces an isomorphism of realizations. -/
@[stacks 012C "isomorphism reflection for the filtered-complex forgetful functor"]
theorem isIso_of_forgetFiltered_map_isIso {S T : Realization (C := C)} (f : S ⟶ T)
    [IsIso ((forgetFiltered (C := C)).map f)] : IsIso f := sorry

/-- The spectral-sequence object underlying a realization is the value of `forgetSequence`. -/
@[simp, stacks 012C "forgetful functor from filtered spectral-sequence realizations"]
theorem forgetSequence_obj (S : Realization (C := C)) :
    (forgetSequence (C := C)).obj S = S.sequence := sorry

/-- The image under `forgetSequence` of a realization map is its spectral-sequence component. -/
@[simp, stacks 012C "forgetful functor from filtered spectral-sequence realizations"]
theorem forgetSequence_map {S T : Realization (C := C)} (f : S ⟶ T) :
    (forgetSequence (C := C)).map f = f.sequenceMap := sorry

/-- The spectral-sequence forgetful functor maps an identity to an identity. -/
@[simp, stacks 012C "identity computation for the spectral-sequence forgetful functor"]
theorem forgetSequence_map_id (S : Realization (C := C)) :
    (forgetSequence (C := C)).map (𝟙 S) = 𝟙 S.sequence := sorry

/-- The spectral-sequence forgetful functor preserves composition. -/
@[simp, reassoc, stacks 012C "composition computation for the spectral-sequence forgetful functor"]
theorem forgetSequence_map_comp
    {S T U : Realization (C := C)} (f : S ⟶ T) (g : T ⟶ U) :
    (forgetSequence (C := C)).map (f ≫ g) =
      (forgetSequence (C := C)).map f ≫ (forgetSequence (C := C)).map g := sorry

end Realization

#synth Category (Realization (C := C))

#synth (Realization.forgetFiltered (C := C)).Faithful

end CategoryTheory.FilteredComplex.SpectralSequence
