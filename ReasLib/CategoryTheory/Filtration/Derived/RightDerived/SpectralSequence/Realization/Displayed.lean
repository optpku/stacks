/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Realization.Map.Reindex
public import ReasLib.CategoryTheory.DisplayedCategory.Transport
public import ReasLib.CategoryTheory.DisplayedCategory.Total

/-!
# Displayed support for unbounded right-derived realizations

The realization maps already form a dependent hom family over filtered-complex morphisms.  This
leaf exposes that family as a `DisplayedCategory`; no chapter-specific wrapper is introduced.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape
open Functor.RightDerived.Homotopy

noncomputable section

universe w wA wB vA vB uA uB

namespace CategoryTheory.FilteredComplex.RightDerived.SpectralSequence

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]

private theorem realizationMap_ext_components
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F]
    {K L : FilteredComplex A} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} {m n : Realization.Map F f S T}
    (hResolution : m.resolutionMap.hom = n.resolutionMap.hom)
    (hSequence : m.sequenceMap = n.sequenceMap) : m = n := by
  rcases m with ⟨⟨r, hr⟩, c, ⟨φ, hφ⟩⟩
  rcases n with ⟨⟨r', hr'⟩, c', ⟨ψ, hψ⟩⟩
  change r = r' at hResolution
  cases hResolution
  change φ = ψ at hSequence
  cases hSequence
  rfl

private theorem realizationMap_reindex_eq_transport
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F]
    {K L : FilteredComplex A} {f g : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (h : f = g)
    (m : Realization.Map F f S T) :
    Realization.Map.reindex F h m = h ▸ m := by
  cases h
  rfl

/-- `[stacks 0BKK]` The dependent category of unbounded right-derived realizations and their maps.
The base category is `FilteredComplex A`, and the displayed hom over `f` is
`Realization.Map F f`. -/
@[stacks 0BKK]
def displayedCategory
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F] :
    DisplayedCategory (FilteredComplex A) where
  obj K := Realization F K
  Hom f S T := Realization.Map F f S T
  id S := Realization.Map.id F S
  comp m n := Realization.Map.comp F m n
  id_comp := fun m => by
    rw [← realizationMap_reindex_eq_transport F]
    apply realizationMap_ext_components F
    · exact Category.id_comp m.resolutionMap.hom
    · exact Category.id_comp m.sequenceMap
  comp_id := fun m => by
    rw [← realizationMap_reindex_eq_transport F]
    apply realizationMap_ext_components F
    · exact Category.comp_id m.resolutionMap.hom
    · exact Category.comp_id m.sequenceMap
  assoc := fun m n k => by
    rw [← realizationMap_reindex_eq_transport F]
    apply realizationMap_ext_components F
    · exact Category.assoc m.resolutionMap.hom n.resolutionMap.hom k.resolutionMap.hom
    · exact Category.assoc m.sequenceMap n.sequenceMap k.sequenceMap

/-- `[stacks 0BKK]` The displayed-object family of unbounded right-derived realizations. -/
@[simp, stacks 0BKK]
theorem displayedCategory_obj
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F] (K : FilteredComplex A) :
    (displayedCategory F).obj K = Realization F K := rfl

/-- `[stacks 0BKK]` The displayed hom family of unbounded right-derived realization maps. -/
@[simp, stacks 0BKK]
theorem displayedCategory_hom
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F]
    {K L : FilteredComplex A} {f : K ⟶ L}
    (S : Realization F K) (T : Realization F L) :
    (displayedCategory F).Hom f S T = Realization.Map F f S T := rfl

/-- `[stacks 0BKK]` The identity operation of the displayed realization category. -/
@[simp, stacks 0BKK]
theorem displayedCategory_id
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F]
    {K : FilteredComplex A} (S : Realization F K) :
    (displayedCategory F).id S = Realization.Map.id F S := rfl

/-- `[stacks 0BKK]` The composition operation of the displayed realization category. -/
@[simp, stacks 0BKK]
theorem displayedCategory_comp
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F]
    {K L M : FilteredComplex A} {f : K ⟶ L} {g : L ⟶ M}
    {R : Realization F K} {S : Realization F L} {T : Realization F M}
    (m : Realization.Map F f R S) (n : Realization.Map F g S T) :
    (displayedCategory F).comp m n = Realization.Map.comp F m n := rfl

/-- `[stacks 0BKK]` Equality transport for maps of unbounded right-derived realizations agrees
with the canonical displayed transport. -/
@[simp, stacks 0BKK]
theorem Realization.Map.reindex_eq_cast
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F]
    {K L : FilteredComplex A} {f g : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (h : f = g)
    (m : Realization.Map F f S T) :
    Realization.Map.reindex F h m =
      DisplayedCategory.Hom.cast (displayedCategory F) h m :=
  realizationMap_reindex_eq_transport F h m

/-- The generic displayed transport can be converted back to the owner-level realization-map
reindexing. -/
@[stacks 0BKK "owner-level transport of unbounded right-derived realization maps"]
theorem Realization.Map.cast_eq_reindex
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F]
    {K L : FilteredComplex A} {f g : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (h : f = g)
    (m : Realization.Map F f S T) :
    DisplayedCategory.Hom.cast (displayedCategory F) h m =
      Realization.Map.reindex F h m :=
  (Realization.Map.reindex_eq_cast F h m).symm

end CategoryTheory.FilteredComplex.RightDerived.SpectralSequence
