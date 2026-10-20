/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Truncation.Naturality.Map.Definition
public import ReasLib.CategoryTheory.DerivedCategory.Preimage.Lift.Operations
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Reindexing truncation-filtration realization maps

The chosen representative lift is part of a realization map, so transport along an equality of
derived morphisms has a single owner and a single family of laws.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe wA wB vA vB uA uB

namespace CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Truncation

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
variable (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
  [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A]

namespace Realization

/-- Reindex a truncation-filtration realization map along an equality of derived morphisms. -/
@[stacks 0BKM "reindexing truncation-filtration realization maps"]
noncomputable def Map.reindex
    {K L : DerivedCategory A} {f g : K ⟶ L}
    {S : Realization F K} {T : Realization F L}
    (h : f = g) (m : Map F f S T) : Map F g S T where
  lift := DerivedCategory.Preimage.Lift.reindex h m.lift
  original := m.original
  pageTwo_hom := sorry
  target_hom := sorry

/-- Reindexing transports the chosen lift along the same equality of derived morphisms. -/
@[simp, stacks 0BKM "lift carried by a reindexed truncation realization map"]
theorem Map.reindex_lift
    {K L : DerivedCategory A} {f g : K ⟶ L}
    {S : Realization F K} {T : Realization F L}
    (h : f = g) (m : Map F f S T) :
    (Map.reindex F h m).lift = DerivedCategory.Preimage.Lift.reindex h m.lift := sorry

/-- Reindexing does not change the cochain map carried by the chosen lift. -/
@[simp, stacks 0BKM "cochain lift of a reindexed truncation realization map"]
theorem Map.reindex_lift_hom
    {K L : DerivedCategory A} {f g : K ⟶ L}
    {S : Realization F K} {T : Realization F L}
    (h : f = g) (m : Map F f S T) :
    (Map.reindex F h m).lift.hom = m.lift.hom := sorry

/-- Reindexing leaves the filtered-model morphism unchanged. -/
@[simp, stacks 0BKM "filtered map after truncation realization reindexing"]
theorem Map.reindex_filteredMap
    {K L : DerivedCategory A} {f g : K ⟶ L}
    {S : Realization F K} {T : Realization F L}
    (h : f = g) (m : Map F f S T) :
    (Map.reindex F h m).filteredMap = m.filteredMap := sorry

/-- Reindexing leaves the renumbered spectral-sequence morphism unchanged. -/
@[simp, stacks 0BKM "spectral-sequence map after truncation realization reindexing"]
theorem Map.reindex_sequenceMap
    {K L : DerivedCategory A} {f g : K ⟶ L}
    {S : Realization F K} {T : Realization F L}
    (h : f = g) (m : Map F f S T) :
    (Map.reindex F h m).sequenceMap = m.sequenceMap := sorry

/-- Reindexing leaves the original generic realization map unchanged. -/
@[simp, stacks 0BKM "original map after truncation realization reindexing"]
theorem Map.reindex_original
    {K L : DerivedCategory A} {f g : K ⟶ L}
    {S : Realization F K} {T : Realization F L}
    (h : f = g) (m : Map F f S T) :
    (Map.reindex F h m).original = m.original := sorry

/-- Reindexing preserves the association morphism after transporting its filtered-map index. -/
@[simp, stacks 0BKM "association morphism after truncation realization reindexing"]
theorem Map.toAssociationHom_reindex
    {K L : DerivedCategory A} {f g : K ⟶ L}
    {S : Realization F K} {T : Realization F L}
    (h : f = g) (m : Map F f S T) :
    ((Map.reindex_filteredMap F h m) ▸ (Map.reindex F h m).toAssociationHom) =
      m.toAssociationHom := sorry

/-- Reindexing along reflexivity fixes a truncation-filtration realization map. -/
@[simp, stacks 0BKM "reflexive transport of a truncation realization map"]
theorem Map.reindex_rfl
    {K L : DerivedCategory A} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Map F f S T) :
    Map.reindex F rfl m = m := sorry

/-- Successive reindexings combine by equality transitivity. -/
@[simp, stacks 0BKM "transitivity of truncation realization-map transport"]
theorem Map.reindex_trans
    {K L : DerivedCategory A} {f f' f'' : K ⟶ L}
    {S : Realization F K} {T : Realization F L}
    (e : f = f') (e' : f' = f'') (m : Map F f S T) :
    Map.reindex F e' (Map.reindex F e m) =
      Map.reindex F (e.trans e') m := sorry

/-- Reindexing along an equality and its inverse recovers the realization map. -/
@[simp, stacks 0BKM "inverse transport of a truncation realization map"]
theorem Map.reindex_symm
    {K L : DerivedCategory A} {f f' : K ⟶ L}
    {S : Realization F K} {T : Realization F L}
    (e : f = f') (m : Map F f S T) :
    Map.reindex F e.symm (Map.reindex F e m) = m := sorry

end Realization

end CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Truncation
