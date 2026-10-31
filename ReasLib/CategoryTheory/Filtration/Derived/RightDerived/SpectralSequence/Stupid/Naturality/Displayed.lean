/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Stupid.Naturality.Laws
public import ReasLib.CategoryTheory.DisplayedCategory.Transport
public import ReasLib.CategoryTheory.DisplayedCategory.Total

/-!
# Displayed support for stupid-filtration realizations

The specialization already has a dependent map type over cochain-complex morphisms.  This leaf
exposes that type as a displayed category so downstream constructions can use canonical transport
and total-category APIs without rebuilding the dependent bookkeeping.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe wA wB vA vB uA uB

namespace CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Stupid

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]

private theorem Realization.Map.cast_eq_of_components
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A]
    {K L : CochainComplex A ℤ} {f g : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (h : f = g)
    (m : Realization.Map F f S T) (n : Realization.Map F g S T)
    (hres : m.original.resolutionMap.hom = n.original.resolutionMap.hom)
    (hseq : m.sequenceMap = n.sequenceMap) : h ▸ m = n := by
  cases h
  rcases m with ⟨⟨⟨f₁, hf₁⟩, hc₁, ⟨s₁, hs₁⟩⟩, hp₁, ht₁⟩
  rcases n with ⟨⟨⟨f₂, hf₂⟩, hc₂, ⟨s₂, hs₂⟩⟩, hp₂, ht₂⟩
  change f₁ = f₂ at hres
  change s₁ = s₂ at hseq
  cases hres
  cases hseq
  rfl

/- The map owner remains in `Naturality.Definition`; this file only supplies categorical packaging. -/
/-- [stacks 0FLK] The displayed category of stupid-filtration realizations and their maps. -/
@[stacks 0FLK]
noncomputable def displayedCategory
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A] :
    DisplayedCategory (CochainComplex A ℤ) where
  obj K := Realization F K
  Hom f S T := Realization.Map F f S T
  id S := Realization.Map.id F S
  comp m n := Realization.Map.comp F m n
  id_comp := fun m => by
    apply Realization.Map.cast_eq_of_components F
    · exact Category.id_comp m.original.resolutionMap.hom
    · exact Category.id_comp m.sequenceMap
  comp_id := fun m => by
    apply Realization.Map.cast_eq_of_components F
    · exact Category.comp_id m.original.resolutionMap.hom
    · exact Category.comp_id m.sequenceMap
  assoc := fun m n k => by
    apply Realization.Map.cast_eq_of_components F
    · exact Category.assoc m.original.resolutionMap.hom
        n.original.resolutionMap.hom k.original.resolutionMap.hom
    · exact Category.assoc m.sequenceMap n.sequenceMap k.sequenceMap

/-- [stacks 0FLK] The displayed-object family for stupid-filtration realizations. -/
@[simp, stacks 0FLK]
theorem displayedCategory_obj
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A]
    (K : CochainComplex A ℤ) :
    (displayedCategory F).obj K = Realization F K := rfl

/-- [stacks 0FLK] The displayed hom family for stupid-filtration realization maps. -/
@[simp, stacks 0FLK]
theorem displayedCategory_hom
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A]
    {K L : CochainComplex A ℤ} {f : K ⟶ L}
    (S : Realization F K) (T : Realization F L) :
    (displayedCategory F).Hom f S T = Realization.Map F f S T := rfl

/-- [stacks 0FLK] The displayed identity operation for stupid-filtration realizations. -/
@[simp, stacks 0FLK]
theorem displayedCategory_id
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A]
    {K : CochainComplex A ℤ} (S : Realization F K) :
    (displayedCategory F).id S = Realization.Map.id F S := rfl

/-- [stacks 0FLK] The displayed composition operation for stupid-filtration realizations. -/
@[simp, stacks 0FLK]
theorem displayedCategory_comp
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A]
    {K L M : CochainComplex A ℤ} {f : K ⟶ L} {g : L ⟶ M}
    {S : Realization F K} {T : Realization F L} {U : Realization F M}
    (m : Realization.Map F f S T) (n : Realization.Map F g T U) :
    (displayedCategory F).comp m n = Realization.Map.comp F m n := rfl

/-- [stacks 0FLK] Equality transport for stupid-filtration maps agrees with displayed transport. -/
@[simp, stacks 0FLK]
theorem Realization.Map.reindex_eq_cast
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A]
    {K L : CochainComplex A ℤ} {f g : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (h : f = g)
    (m : Realization.Map F f S T) :
    Realization.Map.reindex F h m =
      DisplayedCategory.Hom.cast (displayedCategory F) h m := by
  cases h
  rfl

/-- [stacks 0FLK] The inverse bridge from displayed transport to owner-level reindexing. -/
@[stacks 0FLK]
theorem Realization.Map.cast_eq_reindex
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A]
    {K L : CochainComplex A ℤ} {f g : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (h : f = g)
    (m : Realization.Map F f S T) :
    DisplayedCategory.Hom.cast (displayedCategory F) h m =
      Realization.Map.reindex F h m := by
  exact (Realization.Map.reindex_eq_cast F h m).symm

end CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Stupid
