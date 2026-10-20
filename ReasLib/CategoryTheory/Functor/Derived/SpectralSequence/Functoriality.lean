/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Functor.Derived.SpectralSequence.Basic

/-!
# Functoriality of Right-Derived Spectral-Sequence Realizations

This file is the right-derived naming facade for the neutral functorial-abutment realization API.
It preserves the application-facing `T`/`Q` interface while all map data and categorical
operations are owned by `FilteredComplex.SpectralSequence.Realization.WithAbutment.Map`.
-/

@[expose] public section

open CategoryTheory
noncomputable section

universe w v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor.RightDerived.SpectralSequence

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Category.{v₂} B]
  [Abelian A] [Abelian B]
  [HasDerivedCategory.{w} B]

variable (T : A ⥤ B) [T.Additive]
  {E : Type u₃} [Category.{v₃} E]
  (Q : HomotopyCategory.Plus A ⥤ E)
  [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
  [T.toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso A)]

namespace Realization

/-- A morphism of right-derived realizations over a cochain map. -/
@[stacks 015X "map of derived-functor spectral-sequence realizations"]
abbrev Map {K L : CochainComplex.Plus A} (f : K ⟶ L)
    (S : Realization T Q K) (R : Realization T Q L) :=
  FilteredComplex.SpectralSequence.Realization.WithAbutment.Map
    (fun n => abutmentFunctor T Q n) f S R

namespace Map

/-- The generic filtered-realization map underlying a right-derived realization map. -/
@[stacks 015X "underlying map of a derived-functor realization"]
noncomputable abbrev toFilteredMap
    {K L : CochainComplex.Plus A} {f : K ⟶ L}
    {S : Realization T Q K} {R : Realization T Q L} (m : Map T Q f S R) :
    FilteredComplex.SpectralSequence.Realization.Map
      S.toFilteredRealization R.toFilteredRealization :=
  m.toRealizationMap

/-- The generic map retains the filtered-complex component. -/
@[simp, stacks 015X "filtered component of a derived-functor realization map"]
theorem toFilteredMap_filteredMap
    {K L : CochainComplex.Plus A} {f : K ⟶ L}
    {S : Realization T Q K} {R : Realization T Q L} (m : Map T Q f S R) :
    m.toFilteredMap.filteredMap = m.filteredMap := sorry

/-- The generic map retains the spectral-sequence component. -/
@[simp, stacks 015X "spectral-sequence component of a derived-functor realization map"]
theorem toFilteredMap_sequenceMap
    {K L : CochainComplex.Plus A} {f : K ⟶ L}
    {S : Realization T Q K} {R : Realization T Q L} (m : Map T Q f S R) :
    m.toFilteredMap.sequenceMap = m.sequenceMap := sorry

/-- The association morphism underlying a right-derived realization map. -/
@[stacks 015X "association morphism of a derived-functor realization map"]
noncomputable abbrev toAssociationHom
    {K L : CochainComplex.Plus A} {f : K ⟶ L}
    {S : Realization T Q K} {R : Realization T Q L} (m : Map T Q f S R) :
    FilteredComplex.Association.Hom S.association R.association m.filteredMap :=
  FilteredComplex.SpectralSequence.Realization.WithAbutment.Map.toAssociationHom
    (fun n => abutmentFunctor T Q n) m

/-- The association morphism has the same spectral-sequence component as the realization map. -/
@[simp, stacks 015X "association morphism of a derived-functor realization map"]
theorem toAssociationHom_hom
    {K L : CochainComplex.Plus A} {f : K ⟶ L}
    {S : Realization T Q K} {R : Realization T Q L} (m : Map T Q f S R) :
    (toAssociationHom T Q m).hom = m.sequenceMap := sorry

/-- Two right-derived realization maps over the same cochain map are equal when their filtered
and spectral-sequence components agree. -/
@[stacks 015X "extensionality of derived-functor spectral-sequence realization maps"]
theorem ext
    {K L : CochainComplex.Plus A} {f : K ⟶ L}
    {S : Realization T Q K} {R : Realization T Q L} {m n : Map T Q f S R}
    (h_filtered : m.filteredMap = n.filteredMap)
    (h_sequence : m.sequenceMap = n.sequenceMap) : m = n := sorry

/-- A right-derived realization map is determined by its filtered-complex component. -/
@[stacks 015X "extensionality of derived-functor spectral-sequence realization maps"]
theorem ext_filteredMap
    {K L : CochainComplex.Plus A} {f : K ⟶ L}
    {S : Realization T Q K} {R : Realization T Q L} {m n : Map T Q f S R}
    (h_filtered : m.filteredMap = n.filteredMap) : m = n := sorry

/-- Equation form of abutment naturality for a right-derived realization map. -/
@[reassoc, stacks 015X "derived-functor spectral-sequence abutment naturality"]
theorem abutment_hom
    {K L : CochainComplex.Plus A} {f : K ⟶ L}
    {S : Realization T Q K} {R : Realization T Q L}
    (m : Map T Q f S R) (n : ℤ) :
    HomologicalComplex.homologyMap
          (FilteredComplex.underlyingMap m.filteredMap) n ≫
        (R.abutmentIso n).hom =
      (S.abutmentIso n).hom ≫ abutmentMap T Q f n := sorry

/-- The inverse abutment comparisons are natural for a right-derived realization map. -/
@[reassoc, stacks 015X "inverse derived-functor spectral-sequence abutment naturality"]
theorem abutment_inv_naturality
    {K L : CochainComplex.Plus A} {f : K ⟶ L}
    {S : Realization T Q K} {R : Realization T Q L}
    (m : Map T Q f S R) (n : ℤ) :
    abutmentMap T Q f n ≫ (R.abutmentIso n).inv =
      (S.abutmentIso n).inv ≫
        HomologicalComplex.homologyMap
          (FilteredComplex.underlyingMap m.filteredMap) n := sorry

/-- Conjugating the abutment map by the chosen comparisons recovers the underlying homology
map. -/
@[reassoc, stacks 015X "computation of a derived-functor spectral-sequence abutment map"]
theorem abutment_naturality_inv
    {K L : CochainComplex.Plus A} {f : K ⟶ L}
    {S : Realization T Q K} {R : Realization T Q L}
    (m : Map T Q f S R) (n : ℤ) :
    (S.abutmentIso n).hom ≫ abutmentMap T Q f n ≫ (R.abutmentIso n).inv =
      HomologicalComplex.homologyMap
        (FilteredComplex.underlyingMap m.filteredMap) n := sorry

/-- The identity morphism of a right-derived realization. -/
@[stacks 015X "identity map of a derived-functor spectral-sequence realization"]
noncomputable abbrev id {K : CochainComplex.Plus A} (S : Realization T Q K) :
    Map T Q (𝟙 K) S S :=
  FilteredComplex.SpectralSequence.Realization.WithAbutment.Map.id
    (fun n => abutmentFunctor T Q n) S

/-- The generic map underlying the identity is the canonical identity. -/
@[simp, stacks 015X "identity map of a derived-functor spectral-sequence realization"]
theorem id_toFilteredMap {K : CochainComplex.Plus A} (S : Realization T Q K) :
    (id T Q S).toFilteredMap =
      FilteredComplex.SpectralSequence.Realization.Map.id
        S.toFilteredRealization := sorry

/-- The filtered-complex component of the identity realization map is the identity. -/
@[simp, stacks 015X "identity map of a derived-functor spectral-sequence realization"]
theorem id_filteredMap {K : CochainComplex.Plus A} (S : Realization T Q K) :
    (id T Q S).filteredMap = 𝟙 S.filtered := sorry

/-- The spectral-sequence component of the identity realization map is the identity. -/
@[simp, stacks 015X "identity map of a derived-functor spectral-sequence realization"]
theorem id_sequenceMap {K : CochainComplex.Plus A} (S : Realization T Q K) :
    (id T Q S).sequenceMap = 𝟙 S.sequence := sorry

/-- The identity map induces the canonical identity association morphism. -/
@[simp, stacks 015X "identity association morphism of a derived-functor realization"]
theorem toAssociationHom_id {K : CochainComplex.Plus A} (S : Realization T Q K) :
    toAssociationHom T Q (id T Q S) =
      FilteredComplex.Association.Hom.id S.association := sorry

/-- The composite of two right-derived realization maps. -/
@[stacks 015X "composition of derived-functor spectral-sequence realization maps"]
noncomputable abbrev comp
    {K L M : CochainComplex.Plus A} {f : K ⟶ L} {g : L ⟶ M}
    {S : Realization T Q K} {R : Realization T Q L} {U : Realization T Q M}
    (m : Map T Q f S R) (n : Map T Q g R U) : Map T Q (f ≫ g) S U :=
  FilteredComplex.SpectralSequence.Realization.WithAbutment.Map.comp
    (fun n => abutmentFunctor T Q n) m n

/-- The generic map underlying a composite is the composite generic map. -/
@[simp, stacks 015X "composition of derived-functor spectral-sequence realization maps"]
theorem comp_toFilteredMap
    {K L M : CochainComplex.Plus A} {f : K ⟶ L} {g : L ⟶ M}
    {S : Realization T Q K} {R : Realization T Q L} {U : Realization T Q M}
    (m : Map T Q f S R) (n : Map T Q g R U) :
    (comp T Q m n).toFilteredMap =
      FilteredComplex.SpectralSequence.Realization.Map.comp
        m.toFilteredMap n.toFilteredMap := sorry

/-- The filtered-complex component of a composite is the composite filtered map. -/
@[simp, stacks 015X "composition of derived-functor spectral-sequence realization maps"]
theorem comp_filteredMap
    {K L M : CochainComplex.Plus A} {f : K ⟶ L} {g : L ⟶ M}
    {S : Realization T Q K} {R : Realization T Q L} {U : Realization T Q M}
    (m : Map T Q f S R) (n : Map T Q g R U) :
    (comp T Q m n).filteredMap = m.filteredMap ≫ n.filteredMap := sorry

/-- The spectral-sequence component of a composite is the composite sequence map. -/
@[simp, stacks 015X "composition of derived-functor spectral-sequence realization maps"]
theorem comp_sequenceMap
    {K L M : CochainComplex.Plus A} {f : K ⟶ L} {g : L ⟶ M}
    {S : Realization T Q K} {R : Realization T Q L} {U : Realization T Q M}
    (m : Map T Q f S R) (n : Map T Q g R U) :
    (comp T Q m n).sequenceMap = m.sequenceMap ≫ n.sequenceMap := sorry

/-- Composition induces composition of association morphisms. -/
@[simp, stacks 015X "composition of derived-functor association morphisms"]
theorem toAssociationHom_comp
    {K L M : CochainComplex.Plus A} {f : K ⟶ L} {g : L ⟶ M}
    {S : Realization T Q K} {R : Realization T Q L} {U : Realization T Q M}
    (m : Map T Q f S R) (n : Map T Q g R U) :
    toAssociationHom T Q (comp T Q m n) =
      FilteredComplex.Association.Hom.comp
        (toAssociationHom T Q m) (toAssociationHom T Q n) := sorry

/-- Reindex a realization map along an equality of its underlying cochain maps. -/
@[stacks 015X "reindexing derived-functor spectral-sequence realization maps"]
abbrev reindex
    {K L : CochainComplex.Plus A} {f g : K ⟶ L}
    {S : Realization T Q K} {R : Realization T Q L}
    (h : f = g) (m : Map T Q f S R) : Map T Q g S R :=
  FilteredComplex.SpectralSequence.Realization.WithAbutment.Map.reindex
    (fun n => abutmentFunctor T Q n) h m

/-- Reindexing leaves the generic filtered-realization map unchanged. -/
@[simp, stacks 015X "reindexing derived-functor spectral-sequence realization maps"]
theorem reindex_toFilteredMap
    {K L : CochainComplex.Plus A} {f g : K ⟶ L}
    {S : Realization T Q K} {R : Realization T Q L}
    (h : f = g) (m : Map T Q f S R) :
    (reindex T Q h m).toFilteredMap = m.toFilteredMap := sorry

/-- Reindexing leaves the filtered-complex component unchanged. -/
@[simp, stacks 015X "reindexing derived-functor spectral-sequence realization maps"]
theorem reindex_filteredMap
    {K L : CochainComplex.Plus A} {f g : K ⟶ L}
    {S : Realization T Q K} {R : Realization T Q L}
    (h : f = g) (m : Map T Q f S R) :
    (reindex T Q h m).filteredMap = m.filteredMap := sorry

/-- Reindexing leaves the spectral-sequence component unchanged. -/
@[simp, stacks 015X "reindexing derived-functor spectral-sequence realization maps"]
theorem reindex_sequenceMap
    {K L : CochainComplex.Plus A} {f g : K ⟶ L}
    {S : Realization T Q K} {R : Realization T Q L}
    (h : f = g) (m : Map T Q f S R) :
    (reindex T Q h m).sequenceMap = m.sequenceMap := sorry

/-- Reindexing preserves the association morphism after transporting its dependent index. -/
@[simp, stacks 015X "reindexing derived-functor association morphisms"]
theorem toAssociationHom_reindex
    {K L : CochainComplex.Plus A} {f g : K ⟶ L}
    {S : Realization T Q K} {R : Realization T Q L}
    (h : f = g) (m : Map T Q f S R) :
    ((reindex_filteredMap T Q h m) ▸ toAssociationHom T Q (reindex T Q h m)) =
      toAssociationHom T Q m := sorry

/-- Reindexing along reflexivity leaves a realization map unchanged. -/
@[simp, stacks 015X "reindexing derived-functor spectral-sequence realization maps"]
theorem reindex_rfl
    {K L : CochainComplex.Plus A} {f : K ⟶ L}
    {S : Realization T Q K} {R : Realization T Q L} (m : Map T Q f S R) :
    reindex T Q rfl m = m := sorry

/-- The identity realization map is a left identity after reindexing. -/
@[stacks 015X "left identity for derived-functor spectral-sequence realization maps"]
theorem id_comp
    {K L : CochainComplex.Plus A} {f : K ⟶ L}
    {S : Realization T Q K} {R : Realization T Q L} (m : Map T Q f S R) :
    reindex T Q (Category.id_comp f) (comp T Q (id T Q S) m) = m := sorry

/-- The identity realization map is a right identity after reindexing. -/
@[stacks 015X "right identity for derived-functor spectral-sequence realization maps"]
theorem comp_id
    {K L : CochainComplex.Plus A} {f : K ⟶ L}
    {S : Realization T Q K} {R : Realization T Q L} (m : Map T Q f S R) :
    reindex T Q (Category.comp_id f) (comp T Q m (id T Q R)) = m := sorry

/-- Composition of realization maps is associative after reindexing the cochain map. -/
@[stacks 015X "associativity of derived-functor spectral-sequence realization maps"]
theorem assoc
    {K L M N : CochainComplex.Plus A}
    {f : K ⟶ L} {g : L ⟶ M} {h : M ⟶ N}
    {S : Realization T Q K} {R : Realization T Q L}
    {U : Realization T Q M} {V : Realization T Q N}
    (m : Map T Q f S R) (n : Map T Q g R U) (k : Map T Q h U V) :
    reindex T Q (Category.assoc f g h) (comp T Q (comp T Q m n) k) =
      comp T Q m (comp T Q n k) := sorry

end Map

end Realization

end CategoryTheory.Functor.RightDerived.SpectralSequence
