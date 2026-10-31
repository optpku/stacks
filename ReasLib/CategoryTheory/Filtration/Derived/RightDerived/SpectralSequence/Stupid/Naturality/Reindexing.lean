/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Stupid.Naturality.Definition

/-!
# Reindexing Stupid-Filtration Realization Maps

This file transports maps of stupid-filtration realizations along equalities of their underlying
cochain maps and records the resulting component computations.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe wA wB vA vB uA uB

namespace CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Stupid

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
variable (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
  [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A]

namespace Realization

/-- Transport the original generic realization map along an equality of source cochain maps.
This is the ordinary-equality view of the dependent component used by `Map.reindex`. -/
@[stacks 0FLK "transported original map of a stupid-filtration realization"]
noncomputable def Map.reindexOriginal
    {K L : CochainComplex A ℤ} {f g : K ⟶ L}
    {S : Realization F K} {T : Realization F L}
    (h : f = g) (m : Map F f S T) :
    RightDerived.SpectralSequence.Realization.Map F
      (CochainComplex.Stupid.map g) S.original T.original :=
  RightDerived.SpectralSequence.Realization.Map.reindex F
    (congrArg (fun u => CochainComplex.Stupid.map u) h) m.original

/-- Reindex a stupid-filtration realization map along an equality of cochain maps. -/
@[stacks 0FLK "reindexing stupid-filtration realization maps"]
noncomputable def Map.reindex
    {K L : CochainComplex A ℤ} {f g : K ⟶ L}
    {S : Realization F K} {T : Realization F L}
    (h : f = g) (m : Map F f S T) : Map F g S T where
  original := Map.reindexOriginal F h m
  pageOne_hom := by
    cases h
    exact m.pageOne_hom
  target_hom := by
    cases h
    exact m.target_hom

/-- Reindexing preserves the filtered component of a stupid-filtration realization map. -/
@[simp, stacks 0FLK "reindexed filtered map of a stupid-filtration realization"]
theorem Map.reindex_filteredMap
    {K L : CochainComplex A ℤ} {f g : K ⟶ L}
    {S : Realization F K} {T : Realization F L}
    (h : f = g) (m : Map F f S T) :
    (Map.reindex F h m).filteredMap = m.filteredMap := rfl

/-- Reindexing preserves the spectral-sequence component of a stupid-filtration realization
map. -/
@[simp, stacks 0FLK "reindexed spectral-sequence map of a stupid-filtration realization"]
theorem Map.reindex_sequenceMap
    {K L : CochainComplex A ℤ} {f g : K ⟶ L}
    {S : Realization F K} {T : Realization F L}
    (h : f = g) (m : Map F f S T) :
    (Map.reindex F h m).sequenceMap = m.sequenceMap := rfl

/-- The original component of a reindexed stupid-filtration map is its named transported
generic map. -/
@[simp, stacks 0FLK "original map after stupid-filtration reindexing"]
theorem Map.reindex_original
    {K L : CochainComplex A ℤ} {f g : K ⟶ L}
    {S : Realization F K} {T : Realization F L}
    (h : f = g) (m : Map F f S T) :
    (Map.reindex F h m).original = Map.reindexOriginal F h m := rfl

/-- Reindexing the source cochain map preserves the original generic map up to dependent
equality.  Prefer `Map.reindex_original` when an ordinary equality is sufficient. -/
@[stacks 0FLK "dependent original map after stupid-filtration reindexing"]
theorem Map.reindex_original_heq
    {K L : CochainComplex A ℤ} {f g : K ⟶ L}
    {S : Realization F K} {T : Realization F L}
    (h : f = g) (m : Map F f S T) :
    HEq (Map.reindex F h m).original m.original := by
  cases h
  rfl

/-- Reindexing a stupid-filtration map preserves its association morphism. -/
@[simp, stacks 0FLK "reindexing computation for a stupid-filtration association morphism"]
theorem Map.toAssociationHom_reindex
    {K L : CochainComplex A ℤ} {f g : K ⟶ L}
    {S : Realization F K} {T : Realization F L}
    (h : f = g) (m : Map F f S T) :
    ((Map.reindex_filteredMap F h m) ▸
      (Map.reindex F h m).toAssociationHom) = m.toAssociationHom := by
  cases h
  rfl

/-- Successive reindexings of a stupid-filtration realization map combine by transitivity. -/
@[simp, stacks 0FLK "transitivity of stupid-filtration map transport"]
theorem Map.reindex_trans
    {K L : CochainComplex A ℤ} {f f' f'' : K ⟶ L}
    {S : Realization F K} {T : Realization F L}
    (e : f = f') (e' : f' = f'') (m : Map F f S T) :
    Map.reindex F e' (Map.reindex F e m) = Map.reindex F (e.trans e') m := by
  cases e
  cases e'
  rfl

/-- Reindexing along an equality and its inverse recovers a stupid-filtration realization map. -/
@[simp, stacks 0FLK "inverse stupid-filtration map transport"]
theorem Map.reindex_symm
    {K L : CochainComplex A ℤ} {f f' : K ⟶ L}
    {S : Realization F K} {T : Realization F L}
    (e : f = f') (m : Map F f S T) :
    Map.reindex F e.symm (Map.reindex F e m) = m := by
  cases e
  rfl

end Realization

end CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Stupid
