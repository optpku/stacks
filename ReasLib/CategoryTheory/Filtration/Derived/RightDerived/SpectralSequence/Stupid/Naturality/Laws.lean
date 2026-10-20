/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Stupid.Naturality.Composition
public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Stupid.Naturality.Reindexing

/-!
# Laws for Stupid-Filtration Realization Maps

This file records reflexive reindexing, identity, associativity, and extensionality for maps of
stupid-filtration right-derived spectral sequences.
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

/-- Reindexing along reflexivity leaves a stupid-filtration realization map unchanged. -/
@[simp, stacks 0FLK "reflexive reindexing of a stupid-filtration realization map"]
theorem Map.reindex_rfl
    {K L : CochainComplex A ℤ} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Map F f S T) :
    Map.reindex F rfl m = m := sorry

/-- Reindexing the left factor of a composite stupid-filtration map commutes with composition. -/
@[simp, stacks 0FLK "left-factor stupid-filtration map transport"]
theorem Map.reindex_comp_left
    {K L M : CochainComplex A ℤ} {f f' : K ⟶ L} {g : L ⟶ M}
    {S : Realization F K} {T : Realization F L} {U : Realization F M}
    (e : f = f') (m : Map F f S T) (n : Map F g T U) :
    Map.reindex F (congrArg (fun k : K ⟶ L => k ≫ g) e) (Map.comp F m n) =
      Map.comp F (Map.reindex F e m) n := sorry

/-- Reindexing the right factor of a composite stupid-filtration map commutes with composition. -/
@[simp, stacks 0FLK "right-factor stupid-filtration map transport"]
theorem Map.reindex_comp_right
    {K L M : CochainComplex A ℤ} {f : K ⟶ L} {g g' : L ⟶ M}
    {S : Realization F K} {T : Realization F L} {U : Realization F M}
    (e : g = g') (m : Map F f S T) (n : Map F g T U) :
    Map.reindex F (congrArg (fun k : L ⟶ M => f ≫ k) e) (Map.comp F m n) =
      Map.comp F m (Map.reindex F e n) := sorry

/-- Reindexing both factors of a composite stupid-filtration map commutes with composition. -/
@[simp, stacks 0FLK "two-factor stupid-filtration map transport"]
theorem Map.reindex_comp
    {K L M : CochainComplex A ℤ} {f f' : K ⟶ L} {g g' : L ⟶ M}
    {S : Realization F K} {T : Realization F L} {U : Realization F M}
    (e : f = f') (e' : g = g') (m : Map F f S T) (n : Map F g T U) :
    Map.reindex F (congrArg₂ (fun (a : K ⟶ L) (b : L ⟶ M) => a ≫ b) e e')
        (Map.comp F m n) =
      Map.comp F (Map.reindex F e m) (Map.reindex F e' n) := sorry

/-- The identity realization map is a left identity after reindexing the underlying cochain map. -/
@[stacks 0FLK "left identity for stupid-filtration realization maps"]
theorem Map.id_comp
    {K L : CochainComplex A ℤ} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Map F f S T) :
    Map.reindex F (Category.id_comp f) (Map.comp F (Map.id F S) m) = m := sorry

/-- The identity realization map is a right identity after reindexing the underlying cochain map. -/
@[stacks 0FLK "right identity for stupid-filtration realization maps"]
theorem Map.comp_id
    {K L : CochainComplex A ℤ} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Map F f S T) :
    Map.reindex F (Category.comp_id f) (Map.comp F m (Map.id F T)) = m := sorry

/-- Composition of realization maps is associative after reindexing the underlying cochain map. -/
@[stacks 0FLK "associativity of stupid-filtration realization maps"]
theorem Map.assoc
    {K L M N : CochainComplex A ℤ} {f : K ⟶ L} {g : L ⟶ M} {h : M ⟶ N}
    {S : Realization F K} {T : Realization F L}
    {U : Realization F M} {V : Realization F N}
    (m : Map F f S T) (n : Map F g T U) (k : Map F h U V) :
    Map.reindex F (Category.assoc f g h) (Map.comp F (Map.comp F m n) k) =
      Map.comp F m (Map.comp F n k) := sorry

/-- Stupid-filtration realization maps are determined by their underlying generic maps. -/
@[ext, stacks 0FLK "extensionality of stupid-filtration realization maps"]
theorem Map.ext
    {K L : CochainComplex A ℤ} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L}
    {m n : Map F f S T} (h : m.original = n.original) : m = n := sorry

end Realization

end CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Stupid
