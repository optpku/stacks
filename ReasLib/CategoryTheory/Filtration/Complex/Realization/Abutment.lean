module

public import ReasLib.CategoryTheory.Filtration.Complex.Realization

/-!
# Filtered Spectral-Sequence Realizations with a Functorial Abutment

This file extends a generic filtered spectral-sequence realization by a degreewise comparison
with the values of a family of functors.  It is independent of the construction of the filtered
complex and of the mathematical interpretation of the abutment.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v v' u u'

namespace CategoryTheory.FilteredComplex.SpectralSequence.Realization

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {I : Type u'} [Category.{v'} I]

/-- A filtered spectral-sequence realization together with a chosen comparison from the
cohomology of its underlying complex to a functorial degreewise abutment. -/
@[stacks 012C "filtered spectral-sequence realization with functorial abutment"]
structure WithAbutment (H : ℤ → (I ⥤ C)) (X : I)
    extends toRealization : Realization (C := C) where
  /-- The chosen degreewise comparison with the functorial abutment. -/
  abutmentIso : ∀ n : ℤ, filtered.underlying.homology n ≅ (H n).obj X

namespace WithAbutment

variable (H : ℤ → (I ⥤ C))

/-- Forgetting the abutment comparison retains the filtered complex. -/
@[simp, stacks 012C "underlying filtered spectral-sequence realization"]
theorem toRealization_filtered {X : I} (S : WithAbutment H X) :
    S.toRealization.filtered = S.filtered := sorry

/-- Forgetting the abutment comparison retains the spectral sequence. -/
@[simp, stacks 012C "underlying filtered spectral-sequence realization"]
theorem toRealization_sequence {X : I} (S : WithAbutment H X) :
    S.toRealization.sequence = S.sequence := sorry

/-- Forgetting the abutment comparison retains the chosen association. -/
@[simp, stacks 012C "underlying filtered spectral-sequence realization"]
theorem toRealization_association {X : I} (S : WithAbutment H X) :
    S.toRealization.association = S.association := sorry

/-- A realization with a functorial abutment is associated to its filtered complex. -/
@[stacks 012C "association of a filtered realization with functorial abutment"]
theorem isAssociated {X : I} (S : WithAbutment H X) :
    FilteredComplex.IsAssociated S.filtered S.sequence := sorry

/-- A map of filtered spectral-sequence realizations over a morphism of abutment parameters.
The inherited map owns the filtered and spectral-sequence components; the additional square is
exactly the naturality condition for the selected abutment comparisons. -/
@[stacks 012O "map of filtered spectral-sequence realizations with functorial abutment"]
structure Map {X Y : I} (f : X ⟶ Y)
    (S : WithAbutment H X) (T : WithAbutment H Y)
    extends toRealizationMap : Realization.Map S.toRealization T.toRealization where
  /-- Naturality of the selected abutment comparisons. -/
  abutmentSq : ∀ n : ℤ,
    CommSq (HomologicalComplex.homologyMap
        (FilteredComplex.underlyingMap filteredMap) n)
      (S.abutmentIso n).hom (T.abutmentIso n).hom ((H n).map f)

namespace Map

/-- The generic realization map retains the filtered-complex component. -/
@[simp, stacks 012O "filtered component of a realization map with functorial abutment"]
theorem toRealizationMap_filteredMap
    {X Y : I} {f : X ⟶ Y} {S : WithAbutment H X} {T : WithAbutment H Y}
    (m : Map H f S T) :
    m.toRealizationMap.filteredMap = m.filteredMap := sorry

/-- The generic realization map retains the spectral-sequence component. -/
@[simp, stacks 012O "spectral-sequence component of a realization map with functorial abutment"]
theorem toRealizationMap_sequenceMap
    {X Y : I} {f : X ⟶ Y} {S : WithAbutment H X} {T : WithAbutment H Y}
    (m : Map H f S T) :
    m.toRealizationMap.sequenceMap = m.sequenceMap := sorry

/-- The association morphism underlying a realization map with functorial abutment. -/
@[stacks 012O "association morphism of a realization map with functorial abutment"]
def toAssociationHom
    {X Y : I} {f : X ⟶ Y} {S : WithAbutment H X} {T : WithAbutment H Y}
    (m : Map H f S T) :
    FilteredComplex.Association.Hom S.association T.association m.filteredMap :=
  m.toRealizationMap.toAssociationHom

/-- The association morphism has the same spectral-sequence component as the realization map. -/
@[simp, stacks 012O "association morphism of a realization map with functorial abutment"]
theorem toAssociationHom_hom
    {X Y : I} {f : X ⟶ Y} {S : WithAbutment H X} {T : WithAbutment H Y}
    (m : Map H f S T) :
    (toAssociationHom H m).hom = m.sequenceMap := sorry

/-- Maps over the same abutment-parameter morphism are determined by their generic realization
maps; the abutment square is proposition-valued. -/
@[ext, stacks 012O "extensionality of realization maps with functorial abutment"]
theorem ext
    {X Y : I} {f : X ⟶ Y} {S : WithAbutment H X} {T : WithAbutment H Y}
    {m n : Map H f S T} (h : m.toRealizationMap = n.toRealizationMap) :
    m = n := sorry

/-- A realization map with functorial abutment is determined by its filtered-complex
component. -/
@[stacks 012O "extensionality of realization maps with functorial abutment"]
theorem ext_filteredMap
    {X Y : I} {f : X ⟶ Y} {S : WithAbutment H X} {T : WithAbutment H Y}
    {m n : Map H f S T} (h : m.filteredMap = n.filteredMap) :
    m = n := sorry

/-- Equation form of naturality of the selected abutment comparisons. -/
@[reassoc, stacks 012O "naturality of a functorial spectral-sequence abutment"]
theorem abutment_hom
    {X Y : I} {f : X ⟶ Y} {S : WithAbutment H X} {T : WithAbutment H Y}
    (m : Map H f S T) (n : ℤ) :
    HomologicalComplex.homologyMap
          (FilteredComplex.underlyingMap m.filteredMap) n ≫
        (T.abutmentIso n).hom =
      (S.abutmentIso n).hom ≫ (H n).map f := sorry

/-- Naturality of the inverse selected abutment comparisons. -/
@[reassoc, stacks 012O "inverse naturality of a functorial spectral-sequence abutment"]
theorem abutment_inv_naturality
    {X Y : I} {f : X ⟶ Y} {S : WithAbutment H X} {T : WithAbutment H Y}
    (m : Map H f S T) (n : ℤ) :
    (H n).map f ≫ (T.abutmentIso n).inv =
      (S.abutmentIso n).inv ≫
        HomologicalComplex.homologyMap
          (FilteredComplex.underlyingMap m.filteredMap) n := sorry

/-- Conjugating the functorial abutment map by the selected comparisons recovers the map on
cohomology of the underlying filtered complexes. -/
@[reassoc, stacks 012O "computation of a functorial spectral-sequence abutment map"]
theorem abutment_naturality_inv
    {X Y : I} {f : X ⟶ Y} {S : WithAbutment H X} {T : WithAbutment H Y}
    (m : Map H f S T) (n : ℤ) :
    (S.abutmentIso n).hom ≫ (H n).map f ≫ (T.abutmentIso n).inv =
      HomologicalComplex.homologyMap
        (FilteredComplex.underlyingMap m.filteredMap) n := sorry

/-- Conjugating the map on the underlying filtered complex by the inverse abutment comparisons
recovers the functorial abutment map. -/
@[reassoc, stacks 012O "target-map computation of a functorial spectral-sequence abutment"]
theorem abutment_target_map
    {X Y : I} {f : X ⟶ Y} {S : WithAbutment H X} {T : WithAbutment H Y}
    (m : Map H f S T) (n : ℤ) :
    (S.abutmentIso n).inv ≫
        HomologicalComplex.homologyMap
          (FilteredComplex.underlyingMap m.filteredMap) n ≫
      (T.abutmentIso n).hom =
      (H n).map f := sorry

/-- Identity filtered and parameter maps commute with the selected abutment comparisons. -/
@[stacks 012O "identity map of a realization with functorial abutment"]
theorem idAbutment {X : I} (S : WithAbutment H X) :
    ∀ n : ℤ,
      CommSq (HomologicalComplex.homologyMap
          (FilteredComplex.underlyingMap (𝟙 S.filtered)) n)
        (S.abutmentIso n).hom (S.abutmentIso n).hom ((H n).map (𝟙 X)) := sorry

/-- The identity morphism of a realization with functorial abutment. -/
@[stacks 012O "identity map of a realization with functorial abutment"]
noncomputable def id {X : I} (S : WithAbutment H X) : Map H (𝟙 X) S S where
  toRealizationMap := Realization.Map.id S.toRealization
  abutmentSq := idAbutment H S

/-- The generic realization map underlying the identity is the canonical identity. -/
@[simp, stacks 012O "identity map of a realization with functorial abutment"]
theorem id_toRealizationMap {X : I} (S : WithAbutment H X) :
    (id H S).toRealizationMap = Realization.Map.id S.toRealization := sorry

/-- The filtered-complex component of the identity realization map is the identity. -/
@[simp, stacks 012O "identity map of a realization with functorial abutment"]
theorem id_filteredMap {X : I} (S : WithAbutment H X) :
    (id H S).filteredMap = 𝟙 S.filtered := sorry

/-- The spectral-sequence component of the identity realization map is the identity. -/
@[simp, stacks 012O "identity map of a realization with functorial abutment"]
theorem id_sequenceMap {X : I} (S : WithAbutment H X) :
    (id H S).sequenceMap = 𝟙 S.sequence := sorry

/-- The association morphism underlying the identity is the canonical association identity. -/
@[simp, stacks 012O "identity association morphism with functorial abutment"]
theorem toAssociationHom_id {X : I} (S : WithAbutment H X) :
    toAssociationHom H (id H S) =
      FilteredComplex.Association.Hom.id S.association := sorry

/-- Composite filtered and parameter maps commute with the selected abutment comparisons. -/
@[stacks 012O "composition of realization maps with functorial abutment"]
theorem compAbutment
    {X Y Z : I} {f : X ⟶ Y} {g : Y ⟶ Z}
    {S : WithAbutment H X} {T : WithAbutment H Y} {U : WithAbutment H Z}
    (m : Map H f S T) (n : Map H g T U) :
    ∀ k : ℤ,
      CommSq (HomologicalComplex.homologyMap
          (FilteredComplex.underlyingMap (m.filteredMap ≫ n.filteredMap)) k)
        (S.abutmentIso k).hom (U.abutmentIso k).hom ((H k).map (f ≫ g)) := sorry

/-- The composite of two realization maps with functorial abutment. -/
@[stacks 012O "composition of realization maps with functorial abutment"]
noncomputable def comp
    {X Y Z : I} {f : X ⟶ Y} {g : Y ⟶ Z}
    {S : WithAbutment H X} {T : WithAbutment H Y} {U : WithAbutment H Z}
    (m : Map H f S T) (n : Map H g T U) : Map H (f ≫ g) S U where
  toRealizationMap := Realization.Map.comp m.toRealizationMap n.toRealizationMap
  abutmentSq := compAbutment H m n

/-- The generic realization map underlying a composite is the composite map. -/
@[simp, stacks 012O "composition of realization maps with functorial abutment"]
theorem comp_toRealizationMap
    {X Y Z : I} {f : X ⟶ Y} {g : Y ⟶ Z}
    {S : WithAbutment H X} {T : WithAbutment H Y} {U : WithAbutment H Z}
    (m : Map H f S T) (n : Map H g T U) :
    (comp H m n).toRealizationMap =
      Realization.Map.comp m.toRealizationMap n.toRealizationMap := sorry

/-- The filtered-complex component of a composite is the composite filtered map. -/
@[simp, stacks 012O "composition of realization maps with functorial abutment"]
theorem comp_filteredMap
    {X Y Z : I} {f : X ⟶ Y} {g : Y ⟶ Z}
    {S : WithAbutment H X} {T : WithAbutment H Y} {U : WithAbutment H Z}
    (m : Map H f S T) (n : Map H g T U) :
    (comp H m n).filteredMap = m.filteredMap ≫ n.filteredMap := sorry

/-- The spectral-sequence component of a composite is the composite spectral-sequence map. -/
@[simp, stacks 012O "composition of realization maps with functorial abutment"]
theorem comp_sequenceMap
    {X Y Z : I} {f : X ⟶ Y} {g : Y ⟶ Z}
    {S : WithAbutment H X} {T : WithAbutment H Y} {U : WithAbutment H Z}
    (m : Map H f S T) (n : Map H g T U) :
    (comp H m n).sequenceMap = m.sequenceMap ≫ n.sequenceMap := sorry

/-- The association morphism underlying a composite is the composite association morphism. -/
@[simp, stacks 012O "composite association morphism with functorial abutment"]
theorem toAssociationHom_comp
    {X Y Z : I} {f : X ⟶ Y} {g : Y ⟶ Z}
    {S : WithAbutment H X} {T : WithAbutment H Y} {U : WithAbutment H Z}
    (m : Map H f S T) (n : Map H g T U) :
    toAssociationHom H (comp H m n) =
      FilteredComplex.Association.Hom.comp
        (toAssociationHom H m) (toAssociationHom H n) := sorry

/-- Reindex a realization map along an equality of its abutment-parameter morphisms. -/
@[stacks 012O "reindexing realization maps with functorial abutment"]
def reindex
    {X Y : I} {f g : X ⟶ Y} {S : WithAbutment H X} {T : WithAbutment H Y}
    (h : f = g) (m : Map H f S T) : Map H g S T :=
  h ▸ m

/-- Reindexing leaves the underlying generic realization map unchanged. -/
@[simp, stacks 012O "reindexing realization maps with functorial abutment"]
theorem reindex_toRealizationMap
    {X Y : I} {f g : X ⟶ Y} {S : WithAbutment H X} {T : WithAbutment H Y}
    (h : f = g) (m : Map H f S T) :
    (reindex H h m).toRealizationMap = m.toRealizationMap := sorry

/-- Reindexing leaves the filtered-complex component unchanged. -/
@[simp, stacks 012O "reindexing realization maps with functorial abutment"]
theorem reindex_filteredMap
    {X Y : I} {f g : X ⟶ Y} {S : WithAbutment H X} {T : WithAbutment H Y}
    (h : f = g) (m : Map H f S T) :
    (reindex H h m).filteredMap = m.filteredMap := sorry

/-- Reindexing leaves the spectral-sequence component unchanged. -/
@[simp, stacks 012O "reindexing realization maps with functorial abutment"]
theorem reindex_sequenceMap
    {X Y : I} {f g : X ⟶ Y} {S : WithAbutment H X} {T : WithAbutment H Y}
    (h : f = g) (m : Map H f S T) :
    (reindex H h m).sequenceMap = m.sequenceMap := sorry

/-- Reindexing leaves the association morphism unchanged after transporting its dependent
filtered-map index. -/
@[simp, stacks 012O "reindexing association morphisms with functorial abutment"]
theorem toAssociationHom_reindex
    {X Y : I} {f g : X ⟶ Y} {S : WithAbutment H X} {T : WithAbutment H Y}
    (h : f = g) (m : Map H f S T) :
    ((reindex_filteredMap H h m) ▸ toAssociationHom H (reindex H h m)) =
      toAssociationHom H m := sorry

/-- Reindexing along reflexivity leaves a realization map unchanged. -/
@[simp, stacks 012O "reindexing realization maps with functorial abutment"]
theorem reindex_rfl
    {X Y : I} {f : X ⟶ Y} {S : WithAbutment H X} {T : WithAbutment H Y}
    (m : Map H f S T) :
    reindex H rfl m = m := sorry

/-- The identity realization map is a left identity after reindexing the parameter map. -/
@[stacks 012O "left identity for realization maps with functorial abutment"]
theorem id_comp
    {X Y : I} {f : X ⟶ Y} {S : WithAbutment H X} {T : WithAbutment H Y}
    (m : Map H f S T) :
    reindex H (Category.id_comp f) (comp H (id H S) m) = m := sorry

/-- The identity realization map is a right identity after reindexing the parameter map. -/
@[stacks 012O "right identity for realization maps with functorial abutment"]
theorem comp_id
    {X Y : I} {f : X ⟶ Y} {S : WithAbutment H X} {T : WithAbutment H Y}
    (m : Map H f S T) :
    reindex H (Category.comp_id f) (comp H m (id H T)) = m := sorry

/-- Composition of realization maps with functorial abutment is associative after reindexing
the parameter morphism. -/
@[stacks 012O "associativity of realization maps with functorial abutment"]
theorem assoc
    {W X Y Z : I} {f : W ⟶ X} {g : X ⟶ Y} {h : Y ⟶ Z}
    {R : WithAbutment H W} {S : WithAbutment H X}
    {T : WithAbutment H Y} {U : WithAbutment H Z}
    (m : Map H f R S) (n : Map H g S T) (k : Map H h T U) :
    reindex H (Category.assoc f g h) (comp H (comp H m n) k) =
      comp H m (comp H n k) := sorry

end Map

end WithAbutment

end CategoryTheory.FilteredComplex.SpectralSequence.Realization
