module

public import ReasLib.CategoryTheory.DerivedCategory.Ext.SpectralSequence.Source
public import ReasLib.CategoryTheory.DerivedCategory.Ext.SpectralSequence.Functor.Filtered
public import ReasLib.CategoryTheory.Filtration.Complex.Realization

/-!
# Realizations of source-filtered Ext spectral sequences

The generic filtered-complex realization owns the concrete filtered model and its associated
spectral-sequence map.  This source-facing adapter adds only the selected Ext comparisons and
their variance-correct naturality squares.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Pretriangulated ShiftedHom
open scoped DerivedExt

noncomputable section

universe t w v u

namespace CategoryTheory.DerivedCategory.Ext.Source

section Derived

variable {A : Type u} [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{t} A]

/-- A source-filtered Ext realization, with chosen first-page and abutment comparisons. -/
@[stacks 0G1X, stacks 0G1Z]
structure Realization (M : FilteredComplex A) (K : DerivedCategory A) where
  /-- The representation-independent filtered spectral-sequence realization. -/
  original : FilteredComplex.SpectralSequence.Realization
    (C := AddCommGrpCat.{t})
  /-- The original realization has the source-filtered Ext interpretation. -/
  isSpectralSequence :
    IsSpectralSequence M K original.filtered original.sequence
  /-- A chosen first-page comparison with source Ext. -/
  pageOneIso : ∀ p q : ℤ,
    (original.sequence.page 1).X (p, q) ≅
      addCommGrp (DerivedCategory.Q.obj (M.gradedPiece (-p))) K (p + q)
  /-- A chosen comparison from the filtered-model abutment to source Ext. -/
  targetIso : ∀ n : ℤ,
    original.filtered.underlying.homology n ≅
      addCommGrp (DerivedCategory.Q.obj M.underlying) K n

namespace Realization

/-- The filtered complex underlying a source-filtered Ext realization. -/
@[stacks 0G1X, stacks 0G1Z]
noncomputable abbrev filtered {M : FilteredComplex A} {K : DerivedCategory A}
    (S : Realization M K) : FilteredComplex AddCommGrpCat.{t} :=
  S.original.filtered

/-- The spectral sequence underlying a source-filtered Ext realization. -/
@[stacks 0G1X, stacks 0G1Z]
noncomputable abbrev sequence {M : FilteredComplex A} {K : DerivedCategory A}
    (S : Realization M K) : CohomologicalSpectralSequence AddCommGrpCat.{t} 0 :=
  S.original.sequence

/-- The concrete association owned by the generic realization. -/
@[stacks 0G1X, stacks 0G1Z]
noncomputable abbrev association {M : FilteredComplex A} {K : DerivedCategory A}
    (S : Realization M K) :
    FilteredComplex.Association S.filtered S.sequence :=
  S.original.association

/-- The boundedness proof owned by the generic realization. -/
@[stacks 0G1X, stacks 0G1Z]
abbrev bounded {M : FilteredComplex A} {K : DerivedCategory A}
    (S : Realization M K) : S.sequence.IsBounded :=
  S.original.bounded

/-- The finite-filtration proof owned by the generic realization. -/
@[stacks 0G1X, stacks 0G1Z]
abbrev finite {M : FilteredComplex A} {K : DerivedCategory A}
    (S : Realization M K) : FilteredComplex.Cohomology.Filtration.IsFinite S.filtered :=
  S.original.finite

/-- The convergence proof owned by the generic realization. -/
@[stacks 0G1X, stacks 0G1Z]
abbrev converges {M : FilteredComplex A} {K : DerivedCategory A}
    (S : Realization M K) :
    FilteredComplex.Cohomology.Convergence.Converges S.filtered S.sequence :=
  S.original.converges

/-- The source-filtered Ext predicate carried by a realization. -/
@[stacks 0G1X, stacks 0G1Z]
abbrev isSpectral {M : FilteredComplex A} {K : DerivedCategory A}
    (S : Realization M K) : IsSpectralSequence M K S.filtered S.sequence :=
  S.isSpectralSequence

/-- A source-filtered Ext realization is associated to its filtered complex. -/
@[stacks 0G1X, stacks 0G1Z]
theorem isAssociated {M : FilteredComplex A} {K : DerivedCategory A}
    (S : Realization M K) :
    FilteredComplex.IsAssociated S.filtered S.sequence :=
  S.original.isAssociated

/-- The selected first-page comparison satisfies the existence assertion in the Ext predicate. -/
@[stacks 0G1X, stacks 0G1Z]
theorem pageOneIso_nonempty {M : FilteredComplex A} {K : DerivedCategory A}
    (S : Realization M K) (p q : ℤ) :
    Nonempty ((S.sequence.page 1).X (p, q) ≅
      addCommGrp (DerivedCategory.Q.obj (M.gradedPiece (-p))) K (p + q)) :=
  ⟨S.pageOneIso p q⟩

/-- The selected abutment comparison satisfies the inherited realization assertion. -/
@[stacks 0G1X, stacks 0G1Z]
theorem targetIso_nonempty {M : FilteredComplex A} {K : DerivedCategory A}
    (S : Realization M K) (n : ℤ) :
    Nonempty (S.filtered.underlying.homology n ≅
      addCommGrp (DerivedCategory.Q.obj M.underlying) K n) :=
  ⟨S.targetIso n⟩

/- The explicit conditions are arguments of this constructor.  The source predicate is kept
   source-faithful; no page-one boundedness is silently promoted to initial-page boundedness. -/
/-- Build a source Ext realization from a generic bounded model and the Ext convergence criteria.

The selected isomorphisms are obtained from the existential comparisons in `h`; downstream code
should use the named comparison fields rather than inspect the choice. -/
@[stacks 0G1X, stacks 0G1Z]
noncomputable def of
    {M : FilteredComplex A} {K : DerivedCategory A}
    {F : FilteredComplex AddCommGrpCat.{t}}
    {E : CohomologicalSpectralSequence AddCommGrpCat.{t} 0}
    (h : IsSpectralSequence M K F E)
    (hbounded : E.IsBounded)
    (hfinite : FilteredComplex.Cohomology.Filtration.IsFinite F)
    (hvanish : VanishesBelow M K)
    (hstabilize : StabilizesAbove M K) :
    Realization M K where
  original :=
    { filtered := F
      sequence := E
      association := Classical.choice h.associated
      bounded := hbounded
      finite := hfinite
      converges := h.converges hvanish hstabilize }
  isSpectralSequence := h
  pageOneIso := fun p q => Classical.choice (h.pageOne p q)
  targetIso := fun n => Classical.choice (h.abutment n)

/-! ## Maps -/

/-- A map of source-filtered Ext realizations.

For `f : M ⟶ N`, source Ext is contravariant, so the generic realization map runs from the
realization of `N` to that of `M`.  The two additional fields are precisely the first-page and
abutment naturality squares for this variance-correct direction. -/
@[stacks 0G1X, stacks 0G1Z]
structure Map {M N : FilteredComplex A} (f : M ⟶ N)
    {K : DerivedCategory A} (S : Realization M K) (T : Realization N K) where
  /-- The underlying representation-independent realization map, with source variance reversed. -/
  original : FilteredComplex.SpectralSequence.Realization.Map T.original S.original
  /-- Naturality of the selected first-page source-Ext comparisons. -/
  pageOne_hom : ∀ p q : ℤ,
    (original.sequenceMap.hom 1).f (p, q) ≫ (S.pageOneIso p q).hom =
      (T.pageOneIso p q).hom ≫
        (Source.gradedFunctor K (-p) (p + q)).map f.op
  /-- Naturality of the selected source-Ext abutment comparisons. -/
  target_hom : ∀ n : ℤ,
    HomologicalComplex.homologyMap
        (FilteredComplex.underlyingMap original.filteredMap) n ≫
        (S.targetIso n).hom =
      (T.targetIso n).hom ≫ (Source.filteredFunctor K n).map f.op

/-- The filtered-model component of a source Ext realization map. -/
@[stacks 0G1X, stacks 0G1Z]
noncomputable abbrev Map.filteredMap {M N : FilteredComplex A} {f : M ⟶ N}
    {K : DerivedCategory A} {S : Realization M K} {T : Realization N K}
    (m : Map f S T) : T.filtered ⟶ S.filtered :=
  m.original.filteredMap

/-- The spectral-sequence component of a source Ext realization map. -/
@[stacks 0G1X, stacks 0G1Z]
noncomputable abbrev Map.sequenceMap {M N : FilteredComplex A} {f : M ⟶ N}
    {K : DerivedCategory A} {S : Realization M K} {T : Realization N K}
    (m : Map f S T) : T.sequence ⟶ S.sequence :=
  m.original.sequenceMap

/-- The association morphism owned by the generic realization map. -/
@[stacks 0G1X, stacks 0G1Z]
noncomputable abbrev Map.toAssociationHom
    {M N : FilteredComplex A} {f : M ⟶ N}
    {K : DerivedCategory A} {S : Realization M K} {T : Realization N K}
    (m : Map f S T) :
    FilteredComplex.Association.Hom T.association S.association m.filteredMap :=
  m.original.toAssociationHom

/-- The association morphism of a source Ext map has the same (variance-reversed)
spectral-sequence component as the specialized map. -/
@[simp, stacks 0G1X, stacks 0G1Z]
theorem Map.toAssociationHom_hom
    {M N : FilteredComplex A} {f : M ⟶ N}
    {K : DerivedCategory A} {S : Realization M K} {T : Realization N K}
    (m : Map f S T) :
    m.toAssociationHom.hom = m.sequenceMap := sorry

/-- The first-page source naturality square exposed as a theorem. -/
@[reassoc, stacks 0G1X, stacks 0G1Z]
theorem Map.pageOne_naturality {M N : FilteredComplex A} {f : M ⟶ N}
    {K : DerivedCategory A} {S : Realization M K} {T : Realization N K}
    (m : Map f S T) (p q : ℤ) :
    (m.sequenceMap.hom 1).f (p, q) ≫ (S.pageOneIso p q).hom =
      (T.pageOneIso p q).hom ≫
        (Source.gradedFunctor K (-p) (p + q)).map f.op :=
  m.pageOne_hom p q

/-- The source abutment naturality square exposed as a theorem. -/
@[reassoc, stacks 0G1X, stacks 0G1Z]
theorem Map.target_naturality {M N : FilteredComplex A} {f : M ⟶ N}
    {K : DerivedCategory A} {S : Realization M K} {T : Realization N K}
    (m : Map f S T) (n : ℤ) :
    HomologicalComplex.homologyMap
        (FilteredComplex.underlyingMap m.filteredMap) n ≫
        (S.targetIso n).hom =
      (T.targetIso n).hom ≫ (Source.filteredFunctor K n).map f.op :=
  m.target_hom n

/-- The inverse first-page source-Ext comparisons are natural for a realization map. -/
@[reassoc, stacks 0G1X, stacks 0G1Z]
theorem Map.pageOne_inv_naturality {M N : FilteredComplex A} {f : M ⟶ N}
    {K : DerivedCategory A} {S : Realization M K} {T : Realization N K}
    (m : Map f S T) (p q : ℤ) :
    (Source.gradedFunctor K (-p) (p + q)).map f.op ≫ (S.pageOneIso p q).inv =
      (T.pageOneIso p q).inv ≫ (m.sequenceMap.hom 1).f (p, q) := sorry

/-- The inverse source-Ext abutment comparisons are natural for a realization map. -/
@[reassoc, stacks 0G1X, stacks 0G1Z]
theorem Map.target_inv_naturality {M N : FilteredComplex A} {f : M ⟶ N}
    {K : DerivedCategory A} {S : Realization M K} {T : Realization N K}
    (m : Map f S T) (n : ℤ) :
    (Source.filteredFunctor K n).map f.op ≫ (S.targetIso n).inv =
      (T.targetIso n).inv ≫
        HomologicalComplex.homologyMap
          (FilteredComplex.underlyingMap m.filteredMap) n := sorry

/- The inverse form is the computation form normally needed for the contravariant source model. -/
/-- The first-page source-Ext comparison can be inverted to recover the underlying page map. -/
@[reassoc, stacks 0G1X, stacks 0G1Z]
theorem Map.pageOne_naturality_inv {M N : FilteredComplex A} {f : M ⟶ N}
    {K : DerivedCategory A} {S : Realization M K} {T : Realization N K}
    (m : Map f S T) (p q : ℤ) :
    (T.pageOneIso p q).hom ≫
        (Source.gradedFunctor K (-p) (p + q)).map f.op ≫ (S.pageOneIso p q).inv =
      (m.sequenceMap.hom 1).f (p, q) := sorry

/-- The source-Ext abutment comparison can be inverted to recover the underlying homology map. -/
@[reassoc, stacks 0G1X, stacks 0G1Z]
theorem Map.target_naturality_inv {M N : FilteredComplex A} {f : M ⟶ N}
    {K : DerivedCategory A} {S : Realization M K} {T : Realization N K}
    (m : Map f S T) (n : ℤ) :
    (T.targetIso n).hom ≫ (Source.filteredFunctor K n).map f.op ≫ (S.targetIso n).inv =
      HomologicalComplex.homologyMap
        (FilteredComplex.underlyingMap m.filteredMap) n := sorry

/-- The identity map of a source-filtered Ext realization. -/
@[stacks 0G1X, stacks 0G1Z]
noncomputable def Map.id {M : FilteredComplex A} {K : DerivedCategory A}
    (S : Realization M K) : Map (𝟙 M) S S where
  original := FilteredComplex.SpectralSequence.Realization.Map.id S.original
  pageOne_hom := by sorry
  target_hom := by sorry

/-- The identity source Ext realization map has identity filtered component. -/
@[simp, stacks 0G1X, stacks 0G1Z]
theorem Map.id_filteredMap {M : FilteredComplex A} {K : DerivedCategory A}
    (S : Realization M K) :
    (Map.id S).filteredMap = 𝟙 S.filtered := by sorry

/-- The identity source Ext realization map has identity spectral-sequence component. -/
@[simp, stacks 0G1X, stacks 0G1Z]
theorem Map.id_sequenceMap {M : FilteredComplex A} {K : DerivedCategory A}
    (S : Realization M K) :
    (Map.id S).sequenceMap = 𝟙 S.sequence := by sorry

/-- The association morphism of the identity source Ext realization map is the canonical
association identity. -/
@[simp, stacks 0G1X, stacks 0G1Z]
theorem Map.toAssociationHom_id {M : FilteredComplex A} {K : DerivedCategory A}
    (S : Realization M K) :
    (Map.id S).toAssociationHom =
      FilteredComplex.Association.Hom.id S.association := sorry

/-- Compose source-filtered Ext maps.  The generic maps compose in the reverse order dictated by
source variance. -/
@[stacks 0G1X, stacks 0G1Z]
noncomputable def Map.comp
    {M N P : FilteredComplex A} {f : M ⟶ N} {g : N ⟶ P}
    {K : DerivedCategory A} {S : Realization M K} {T : Realization N K}
    {U : Realization P K} (m : Map f S T) (n : Map g T U) :
    Map (f ≫ g) S U where
  original := FilteredComplex.SpectralSequence.Realization.Map.comp n.original m.original
  pageOne_hom := by sorry
  target_hom := by sorry

/-- The filtered-model component of a composite source Ext map. -/
@[simp, stacks 0G1X, stacks 0G1Z]
theorem Map.comp_filteredMap
    {M N P : FilteredComplex A} {f : M ⟶ N} {g : N ⟶ P}
    {K : DerivedCategory A} {S : Realization M K} {T : Realization N K}
    {U : Realization P K} (m : Map f S T) (n : Map g T U) :
    (Map.comp m n).filteredMap = n.filteredMap ≫ m.filteredMap := by sorry

/-- The spectral-sequence component of a composite source Ext map. -/
@[simp, stacks 0G1X, stacks 0G1Z]
theorem Map.comp_sequenceMap
    {M N P : FilteredComplex A} {f : M ⟶ N} {g : N ⟶ P}
    {K : DerivedCategory A} {S : Realization M K} {T : Realization N K}
    {U : Realization P K} (m : Map f S T) (n : Map g T U) :
    (Map.comp m n).sequenceMap = n.sequenceMap ≫ m.sequenceMap := by sorry

/-- The association morphism of a composite source Ext realization map composes in the reverse
order forced by contravariance in the source variable. -/
@[simp, stacks 0G1X, stacks 0G1Z]
theorem Map.toAssociationHom_comp
    {M N P : FilteredComplex A} {f : M ⟶ N} {g : N ⟶ P}
    {K : DerivedCategory A} {S : Realization M K} {T : Realization N K}
    {U : Realization P K} (m : Map f S T) (n : Map g T U) :
    (Map.comp m n).toAssociationHom =
      FilteredComplex.Association.Hom.comp n.toAssociationHom m.toAssociationHom := sorry

/-- Extensionality for source Ext realization maps; the naturality fields are propositions. -/
@[ext, stacks 0G1X, stacks 0G1Z]
theorem Map.ext
    {M N : FilteredComplex A} {f : M ⟶ N}
    {K : DerivedCategory A} {S : Realization M K} {T : Realization N K}
    {m n : Map f S T} (h : m.original = n.original) : m = n := by sorry

/-- Compatible source Ext realization maps, when the concrete choices and naturality squares
exist, can be packaged without exposing their witnesses. -/
@[stacks 0G1X, stacks 0G1Z]
theorem existsMap [IsGrothendieckAbelian.{w} A]
    {M N : FilteredComplex A} {K : DerivedCategory A} (f : M ⟶ N) :
    ∃ (S : Realization M K) (T : Realization N K), Nonempty (Map f S T) := sorry

end Realization

end Derived

end CategoryTheory.DerivedCategory.Ext.Source
