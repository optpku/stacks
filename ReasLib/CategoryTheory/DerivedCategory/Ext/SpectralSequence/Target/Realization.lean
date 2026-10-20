/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Ext.SpectralSequence.Target
public import ReasLib.CategoryTheory.DerivedCategory.Ext.SpectralSequence.Functor.Filtered
public import ReasLib.CategoryTheory.Filtration.Complex.Realization

/-!
# Realizations of target-filtered Ext spectral sequences

This leaf is an adapter around the representation-independent filtered-complex realization.
The generic realization remains the owner of filtered complexes, spectral sequences, and their
association maps.  The target specialization only records the two comparisons used by Ext
applications and the naturality conditions needed to transport them across a map.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Pretriangulated ShiftedHom
open scoped DerivedExt

noncomputable section

universe t w v u

namespace CategoryTheory.DerivedCategory.Ext.Target

section Derived

variable {A : Type u} [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{t} A]

/- The generic object is deliberately kept behind `original`; this avoids a second owner for the
   filtered complex and its association data. -/
/-- A target-filtered Ext realization, with chosen first-page and abutment comparisons. -/
@[stacks 0G1X, stacks 0G1Y, stacks 0G1Z, stacks 0G20]
structure Realization (M : DerivedCategory A) (K : FilteredComplex A) where
  /-- The representation-independent filtered spectral-sequence realization. -/
  original : FilteredComplex.SpectralSequence.Realization
    (C := AddCommGrpCat.{t})
  /-- The original realization has the target-filtered Ext interpretation. -/
  isSpectralSequence :
    IsSpectralSequence M K original.filtered original.sequence
  /-- A chosen first-page comparison with target Ext. -/
  pageOneIso : ∀ p q : ℤ,
    (original.sequence.page 1).X (p, q) ≅
      addCommGrp M (DerivedCategory.Q.obj (K.gradedPiece p)) (p + q)
  /-- A chosen comparison from the filtered-model abutment to target Ext. -/
  targetIso : ∀ n : ℤ,
    original.filtered.underlying.homology n ≅
      addCommGrp M (DerivedCategory.Q.obj K.underlying) n

namespace Realization

/-- The filtered complex underlying a target-filtered Ext realization. -/
@[stacks 0G1X, stacks 0G1Y, stacks 0G1Z, stacks 0G20]
noncomputable abbrev filtered {M : DerivedCategory A} {K : FilteredComplex A}
    (S : Realization M K) : FilteredComplex AddCommGrpCat.{t} :=
  S.original.filtered

/-- The spectral sequence underlying a target-filtered Ext realization. -/
@[stacks 0G1X, stacks 0G1Y, stacks 0G1Z, stacks 0G20]
noncomputable abbrev sequence {M : DerivedCategory A} {K : FilteredComplex A}
    (S : Realization M K) : CohomologicalSpectralSequence AddCommGrpCat.{t} 0 :=
  S.original.sequence

/-- The concrete association owned by the generic realization. -/
@[stacks 0G1X, stacks 0G1Y, stacks 0G1Z, stacks 0G20]
noncomputable abbrev association {M : DerivedCategory A} {K : FilteredComplex A}
    (S : Realization M K) :
    FilteredComplex.Association S.filtered S.sequence :=
  S.original.association

/-- The boundedness proof owned by the generic realization. -/
@[stacks 0G1X, stacks 0G1Y, stacks 0G1Z, stacks 0G20]
abbrev bounded {M : DerivedCategory A} {K : FilteredComplex A}
    (S : Realization M K) : S.sequence.IsBounded :=
  S.original.bounded

/-- The finite-filtration proof owned by the generic realization. -/
@[stacks 0G1X, stacks 0G1Y, stacks 0G1Z, stacks 0G20]
abbrev finite {M : DerivedCategory A} {K : FilteredComplex A}
    (S : Realization M K) : FilteredComplex.Cohomology.Filtration.IsFinite S.filtered :=
  S.original.finite

/-- The convergence proof owned by the generic realization. -/
@[stacks 0G1X, stacks 0G1Y, stacks 0G1Z, stacks 0G20]
abbrev converges {M : DerivedCategory A} {K : FilteredComplex A}
    (S : Realization M K) :
    FilteredComplex.Cohomology.Convergence.Converges S.filtered S.sequence :=
  S.original.converges

/-- The target-filtered Ext predicate carried by a realization. -/
@[stacks 0G1X, stacks 0G1Y, stacks 0G1Z, stacks 0G20]
abbrev isSpectral {M : DerivedCategory A} {K : FilteredComplex A}
    (S : Realization M K) : IsSpectralSequence M K S.filtered S.sequence :=
  S.isSpectralSequence

/-- A target-filtered Ext realization is associated to its filtered complex. -/
@[stacks 0G1X, stacks 0G1Y, stacks 0G1Z, stacks 0G20]
theorem isAssociated {M : DerivedCategory A} {K : FilteredComplex A}
    (S : Realization M K) :
    FilteredComplex.IsAssociated S.filtered S.sequence :=
  S.original.isAssociated

/-- The selected first-page comparison satisfies the existence assertion in the Ext predicate. -/
@[stacks 0G1X, stacks 0G1Y, stacks 0G1Z, stacks 0G20]
theorem pageOneIso_nonempty {M : DerivedCategory A} {K : FilteredComplex A}
    (S : Realization M K) (p q : ℤ) :
    Nonempty ((S.sequence.page 1).X (p, q) ≅
      addCommGrp M (DerivedCategory.Q.obj (K.gradedPiece p)) (p + q)) :=
  ⟨S.pageOneIso p q⟩

/-- The selected abutment comparison satisfies the inherited realization assertion. -/
@[stacks 0G1X, stacks 0G1Y, stacks 0G1Z, stacks 0G20]
theorem targetIso_nonempty {M : DerivedCategory A} {K : FilteredComplex A}
    (S : Realization M K) (n : ℤ) :
    Nonempty (S.filtered.underlying.homology n ≅
      addCommGrp M (DerivedCategory.Q.obj K.underlying) n) :=
  ⟨S.targetIso n⟩

/- The explicit conditions are intentionally arguments of this constructor.  In particular,
   `IsSpectralSequence.bounded` controls `Page.One.ofZero`, not automatically the initial page
   boundedness required by the generic concrete realization. -/
/-- Build a target Ext realization from a generic bounded model and the Ext convergence criteria.

The selected isomorphisms are obtained from the existential comparisons in `h`; downstream code
should use the named comparison fields rather than inspect the choice. -/
@[stacks 0G1X, stacks 0G1Y, stacks 0G1Z, stacks 0G20]
noncomputable def of
    {M : DerivedCategory A} {K : FilteredComplex A}
    {F : FilteredComplex AddCommGrpCat.{t}}
    {E : CohomologicalSpectralSequence AddCommGrpCat.{t} 0}
    (h : IsSpectralSequence M K F E)
    (hbounded : E.IsBounded)
    (hfinite : FilteredComplex.Cohomology.Filtration.IsFinite F)
    (hvanish : VanishesAbove M K)
    (hstabilize : StabilizesBelow M K) :
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

/-- A map of target-filtered Ext realizations.

The generic realization map carries the concrete filtered and page morphisms.  The two additional
fields are exactly the target-Ext first-page and abutment naturality squares; no new spectral
sequence data is duplicated here. -/
@[stacks 0G1X, stacks 0G1Y, stacks 0G1Z, stacks 0G20]
structure Map {K L : FilteredComplex A} (f : K ⟶ L)
    {M : DerivedCategory A} (S : Realization M K) (T : Realization M L) where
  /-- The underlying representation-independent realization map. -/
  original : FilteredComplex.SpectralSequence.Realization.Map S.original T.original
  /-- Naturality of the selected first-page target-Ext comparisons. -/
  pageOne_hom : ∀ p q : ℤ,
    (original.sequenceMap.hom 1).f (p, q) ≫ (T.pageOneIso p q).hom =
      (S.pageOneIso p q).hom ≫
        (Target.gradedFunctor M p (p + q)).map f
  /-- Naturality of the selected target-Ext abutment comparisons. -/
  target_hom : ∀ n : ℤ,
    HomologicalComplex.homologyMap
        (FilteredComplex.underlyingMap original.filteredMap) n ≫
        (T.targetIso n).hom =
      (S.targetIso n).hom ≫ (Target.filteredFunctor M n).map f

/-- The filtered-model component of a target Ext realization map. -/
@[stacks 0G1X, stacks 0G1Y, stacks 0G1Z, stacks 0G20]
noncomputable abbrev Map.filteredMap {K L : FilteredComplex A} {f : K ⟶ L}
    {M : DerivedCategory A} {S : Realization M K} {T : Realization M L}
    (m : Map f S T) : S.filtered ⟶ T.filtered :=
  m.original.filteredMap

/-- The spectral-sequence component of a target Ext realization map. -/
@[stacks 0G1X, stacks 0G1Y, stacks 0G1Z, stacks 0G20]
noncomputable abbrev Map.sequenceMap {K L : FilteredComplex A} {f : K ⟶ L}
    {M : DerivedCategory A} {S : Realization M K} {T : Realization M L}
    (m : Map f S T) : S.sequence ⟶ T.sequence :=
  m.original.sequenceMap

/-- The association morphism owned by the generic realization map. -/
@[stacks 0G1X, stacks 0G1Y, stacks 0G1Z, stacks 0G20]
noncomputable abbrev Map.toAssociationHom
    {K L : FilteredComplex A} {f : K ⟶ L}
    {M : DerivedCategory A} {S : Realization M K} {T : Realization M L}
    (m : Map f S T) :
    FilteredComplex.Association.Hom S.association T.association m.filteredMap :=
  m.original.toAssociationHom

/-- The association morphism of a target Ext map has the same spectral-sequence component as the
specialized map. -/
@[simp, stacks 0G1X, stacks 0G1Y, stacks 0G1Z, stacks 0G20]
theorem Map.toAssociationHom_hom
    {K L : FilteredComplex A} {f : K ⟶ L}
    {M : DerivedCategory A} {S : Realization M K} {T : Realization M L}
    (m : Map f S T) :
    m.toAssociationHom.hom = m.sequenceMap := sorry

/-- The first-page naturality square exposed as a theorem. -/
@[reassoc, stacks 0G1X, stacks 0G1Y, stacks 0G1Z, stacks 0G20]
theorem Map.pageOne_naturality {K L : FilteredComplex A} {f : K ⟶ L}
    {M : DerivedCategory A} {S : Realization M K} {T : Realization M L}
    (m : Map f S T) (p q : ℤ) :
    (m.sequenceMap.hom 1).f (p, q) ≫ (T.pageOneIso p q).hom =
      (S.pageOneIso p q).hom ≫
        (Target.gradedFunctor M p (p + q)).map f :=
  m.pageOne_hom p q

/-- The abutment naturality square exposed as a theorem. -/
@[reassoc, stacks 0G1X, stacks 0G1Y, stacks 0G1Z, stacks 0G20]
theorem Map.target_naturality {K L : FilteredComplex A} {f : K ⟶ L}
    {M : DerivedCategory A} {S : Realization M K} {T : Realization M L}
    (m : Map f S T) (n : ℤ) :
    HomologicalComplex.homologyMap
        (FilteredComplex.underlyingMap m.filteredMap) n ≫
        (T.targetIso n).hom =
      (S.targetIso n).hom ≫ (Target.filteredFunctor M n).map f :=
  m.target_hom n

/-- Naturality of the inverse first-page target-Ext comparison. -/
@[reassoc, stacks 0G1X, stacks 0G1Y, stacks 0G1Z, stacks 0G20]
theorem Map.pageOne_inv_naturality {K L : FilteredComplex A} {f : K ⟶ L}
    {M : DerivedCategory A} {S : Realization M K} {T : Realization M L}
    (m : Map f S T) (p q : ℤ) :
    (Target.gradedFunctor M p (p + q)).map f ≫ (T.pageOneIso p q).inv =
      (S.pageOneIso p q).inv ≫ (m.sequenceMap.hom 1).f (p, q) := sorry

/-- Naturality of the inverse target-Ext abutment comparison. -/
@[reassoc, stacks 0G1X, stacks 0G1Y, stacks 0G1Z, stacks 0G20]
theorem Map.target_inv_naturality {K L : FilteredComplex A} {f : K ⟶ L}
    {M : DerivedCategory A} {S : Realization M K} {T : Realization M L}
    (m : Map f S T) (n : ℤ) :
    (Target.filteredFunctor M n).map f ≫ (T.targetIso n).inv =
      (S.targetIso n).inv ≫
        HomologicalComplex.homologyMap
          (FilteredComplex.underlyingMap m.filteredMap) n := sorry

/- The inverse form is the computation form normally needed when a page map is written between
   the selected Ext models rather than between the abstract spectral-sequence entries. -/
/-- The first-page target-Ext comparison can be inverted to recover the underlying page map. -/
@[reassoc, stacks 0G1X, stacks 0G1Y, stacks 0G1Z, stacks 0G20]
theorem Map.pageOne_naturality_inv {K L : FilteredComplex A} {f : K ⟶ L}
    {M : DerivedCategory A} {S : Realization M K} {T : Realization M L}
    (m : Map f S T) (p q : ℤ) :
    (S.pageOneIso p q).hom ≫
        (Target.gradedFunctor M p (p + q)).map f ≫ (T.pageOneIso p q).inv =
      (m.sequenceMap.hom 1).f (p, q) := sorry

/-- The target-Ext abutment comparison can be inverted to recover the underlying homology map. -/
@[reassoc, stacks 0G1X, stacks 0G1Y, stacks 0G1Z, stacks 0G20]
theorem Map.target_naturality_inv {K L : FilteredComplex A} {f : K ⟶ L}
    {M : DerivedCategory A} {S : Realization M K} {T : Realization M L}
    (m : Map f S T) (n : ℤ) :
    (S.targetIso n).hom ≫ (Target.filteredFunctor M n).map f ≫ (T.targetIso n).inv =
      HomologicalComplex.homologyMap
        (FilteredComplex.underlyingMap m.filteredMap) n := sorry

/-- The identity map of a target-filtered Ext realization. -/
@[stacks 0G1X, stacks 0G1Y, stacks 0G1Z, stacks 0G20]
noncomputable def Map.id {K : FilteredComplex A} {M : DerivedCategory A}
    (S : Realization M K) : Map (𝟙 K) S S where
  original := FilteredComplex.SpectralSequence.Realization.Map.id S.original
  pageOne_hom := by sorry
  target_hom := by sorry

/-- The identity target Ext realization map has identity filtered component. -/
@[simp, stacks 0G1X, stacks 0G1Y, stacks 0G1Z, stacks 0G20]
theorem Map.id_filteredMap {K : FilteredComplex A} {M : DerivedCategory A}
    (S : Realization M K) :
    (Map.id S).filteredMap = 𝟙 S.filtered := by sorry

/-- The identity target Ext realization map has identity spectral-sequence component. -/
@[simp, stacks 0G1X, stacks 0G1Y, stacks 0G1Z, stacks 0G20]
theorem Map.id_sequenceMap {K : FilteredComplex A} {M : DerivedCategory A}
    (S : Realization M K) :
    (Map.id S).sequenceMap = 𝟙 S.sequence := by sorry

/-- The association morphism of the identity target Ext realization map is the canonical
association identity. -/
@[simp, stacks 0G1X, stacks 0G1Y, stacks 0G1Z, stacks 0G20]
theorem Map.toAssociationHom_id {K : FilteredComplex A} {M : DerivedCategory A}
    (S : Realization M K) :
    (Map.id S).toAssociationHom =
      FilteredComplex.Association.Hom.id S.association := sorry

/-- Compose maps of target-filtered Ext realizations. -/
@[stacks 0G1X, stacks 0G1Y, stacks 0G1Z, stacks 0G20]
noncomputable def Map.comp
    {K L N : FilteredComplex A} {f : K ⟶ L} {g : L ⟶ N}
    {M : DerivedCategory A} {S : Realization M K} {T : Realization M L}
    {U : Realization M N} (m : Map f S T) (n : Map g T U) :
    Map (f ≫ g) S U where
  original := FilteredComplex.SpectralSequence.Realization.Map.comp m.original n.original
  pageOne_hom := by sorry
  target_hom := by sorry

/-- The filtered-model component of a composite target Ext map. -/
@[simp, stacks 0G1X, stacks 0G1Y, stacks 0G1Z, stacks 0G20]
theorem Map.comp_filteredMap
    {K L N : FilteredComplex A} {f : K ⟶ L} {g : L ⟶ N}
    {M : DerivedCategory A} {S : Realization M K} {T : Realization M L}
    {U : Realization M N} (m : Map f S T) (n : Map g T U) :
    (Map.comp m n).filteredMap = m.filteredMap ≫ n.filteredMap := by sorry

/-- The spectral-sequence component of a composite target Ext map. -/
@[simp, stacks 0G1X, stacks 0G1Y, stacks 0G1Z, stacks 0G20]
theorem Map.comp_sequenceMap
    {K L N : FilteredComplex A} {f : K ⟶ L} {g : L ⟶ N}
    {M : DerivedCategory A} {S : Realization M K} {T : Realization M L}
    {U : Realization M N} (m : Map f S T) (n : Map g T U) :
    (Map.comp m n).sequenceMap = m.sequenceMap ≫ n.sequenceMap := by sorry

/-- The association morphism of a composite target Ext realization map is the composite of the
specialized association morphisms. -/
@[simp, stacks 0G1X, stacks 0G1Y, stacks 0G1Z, stacks 0G20]
theorem Map.toAssociationHom_comp
    {K L N : FilteredComplex A} {f : K ⟶ L} {g : L ⟶ N}
    {M : DerivedCategory A} {S : Realization M K} {T : Realization M L}
    {U : Realization M N} (m : Map f S T) (n : Map g T U) :
    (Map.comp m n).toAssociationHom =
      FilteredComplex.Association.Hom.comp m.toAssociationHom n.toAssociationHom := sorry

/-- Extensionality for target Ext realization maps; the naturality fields are propositions. -/
@[ext, stacks 0G1X, stacks 0G1Y, stacks 0G1Z, stacks 0G20]
theorem Map.ext
    {K L : FilteredComplex A} {f : K ⟶ L}
    {M : DerivedCategory A} {S : Realization M K} {T : Realization M L}
    {m n : Map f S T} (h : m.original = n.original) : m = n := by sorry

/-- Compatible target Ext realization maps, when the concrete choices and naturality squares
exist, can be packaged without exposing their witnesses. -/
@[stacks 0G1X, stacks 0G1Y, stacks 0G1Z, stacks 0G20]
theorem existsMap [IsGrothendieckAbelian.{w} A]
    {M : DerivedCategory A} {K L : FilteredComplex A} (f : K ⟶ L) :
    ∃ (S : Realization M K) (T : Realization M L), Nonempty (Map f S T) := sorry

end Realization

end Derived

end CategoryTheory.DerivedCategory.Ext.Target
