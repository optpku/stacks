/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Truncation.Naturality.Map.Laws
public import ReasLib.CategoryTheory.DisplayedCategory.Transport
public import ReasLib.CategoryTheory.DisplayedCategory.Total

/-!
# Displayed support for truncation-filtration realizations

The representative lift is owned by `Realization.Map`, so the displayed hom fiber is the map type
itself.  This keeps truncation realizations aligned with the generic and stupid-filtration
displayed categories.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe wA wB vA vB uA uB

namespace CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Truncation

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]

/-- Owner-level reindexing is primitive equality transport in the realization-map family. -/
theorem Realization.Map.reindex_eq_transport
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A]
    {K L : DerivedCategory A} {f g : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (h : f = g)
    (m : Realization.Map F f S T) :
    Realization.Map.reindex F h m = h ▸ m := by
  cases h
  rfl

/-- [stacks 0BKM] The displayed category of truncation-filtration realizations and their maps. -/
@[stacks 0BKM]
noncomputable def displayedCategory
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A] :
    DisplayedCategory (DerivedCategory A) where
  obj K := Realization F K
  Hom f S T := Realization.Map F f S T
  id S := Realization.Map.id F S
  comp m n := Realization.Map.comp F m n
  id_comp m :=
    (Realization.Map.reindex_eq_transport F (Category.id_comp _) _).symm.trans
      (Realization.Map.id_comp F m)
  comp_id m :=
    (Realization.Map.reindex_eq_transport F (Category.comp_id _) _).symm.trans
      (Realization.Map.comp_id F m)
  assoc a b c :=
    (Realization.Map.reindex_eq_transport F (Category.assoc _ _ _) _).symm.trans
      (Realization.Map.assoc F a b c)

/-- [stacks 0BKM] The displayed-object family for truncation-filtration realizations. -/
@[simp, stacks 0BKM]
theorem displayedCategory_obj
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A]
    (K : DerivedCategory A) :
    (displayedCategory F).obj K = Realization F K := rfl

/-- [stacks 0BKM] The displayed hom family is the bundled realization-map type. -/
@[simp, stacks 0BKM]
theorem displayedCategory_hom
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A]
    {K L : DerivedCategory A} {f : K ⟶ L}
    (S : Realization F K) (T : Realization F L) :
    (displayedCategory F).Hom f S T = Realization.Map F f S T := rfl

/-- [stacks 0BKM] The displayed identity is the bundled identity realization map. -/
@[simp, stacks 0BKM]
theorem displayedCategory_id
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A]
    {K : DerivedCategory A} (S : Realization F K) :
    (displayedCategory F).id S = Realization.Map.id F S := rfl

/-- [stacks 0BKM] Displayed composition is the bundled realization-map composition. -/
@[simp, stacks 0BKM]
theorem displayedCategory_comp
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A]
    {K L M : DerivedCategory A} {f : K ⟶ L} {g : L ⟶ M}
    {S : Realization F K} {T : Realization F L} {U : Realization F M}
    (m : Realization.Map F f S T) (n : Realization.Map F g T U) :
    (displayedCategory F).comp m n = Realization.Map.comp F m n := rfl

/-- [stacks 0BKM] Reindexing agrees with canonical displayed-category transport. -/
@[simp, stacks 0BKM]
theorem Realization.Map.reindex_eq_cast
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A]
    {K L : DerivedCategory A} {f g : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (h : f = g)
    (m : Realization.Map F f S T) :
    Realization.Map.reindex F h m =
      DisplayedCategory.Hom.cast (displayedCategory F) h m :=
  Realization.Map.reindex_eq_transport F h m

/-- [stacks 0BKM] Displayed transport can be expressed using owner-level reindexing. -/
@[stacks 0BKM]
theorem Realization.Map.cast_eq_reindex
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A]
    {K L : DerivedCategory A} {f g : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (h : f = g)
    (m : Realization.Map F f S T) :
    DisplayedCategory.Hom.cast (displayedCategory F) h m =
      Realization.Map.reindex F h m :=
  (Realization.Map.reindex_eq_cast F h m).symm

end CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Truncation
