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
  id_comp := fun _ => sorry
  comp_id := fun _ => sorry
  assoc := fun _ _ _ => sorry

/-- [stacks 0FLK] The displayed-object family for stupid-filtration realizations. -/
@[simp, stacks 0FLK]
theorem displayedCategory_obj
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A]
    (K : CochainComplex A ℤ) :
    (displayedCategory F).obj K = Realization F K := sorry

/-- [stacks 0FLK] The displayed hom family for stupid-filtration realization maps. -/
@[simp, stacks 0FLK]
theorem displayedCategory_hom
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A]
    {K L : CochainComplex A ℤ} {f : K ⟶ L}
    (S : Realization F K) (T : Realization F L) :
    (displayedCategory F).Hom f S T = Realization.Map F f S T := sorry

/-- [stacks 0FLK] The displayed identity operation for stupid-filtration realizations. -/
@[simp, stacks 0FLK]
theorem displayedCategory_id
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A]
    {K : CochainComplex A ℤ} (S : Realization F K) :
    (displayedCategory F).id S = Realization.Map.id F S := sorry

/-- [stacks 0FLK] The displayed composition operation for stupid-filtration realizations. -/
@[simp, stacks 0FLK]
theorem displayedCategory_comp
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A]
    {K L M : CochainComplex A ℤ} {f : K ⟶ L} {g : L ⟶ M}
    {S : Realization F K} {T : Realization F L} {U : Realization F M}
    (m : Realization.Map F f S T) (n : Realization.Map F g T U) :
    (displayedCategory F).comp m n = Realization.Map.comp F m n := sorry

/-- [stacks 0FLK] Equality transport for stupid-filtration maps agrees with displayed transport. -/
@[simp, stacks 0FLK]
theorem Realization.Map.reindex_eq_cast
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A]
    {K L : CochainComplex A ℤ} {f g : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (h : f = g)
    (m : Realization.Map F f S T) :
    Realization.Map.reindex F h m =
      DisplayedCategory.Hom.cast (displayedCategory F) h m := sorry

/-- [stacks 0FLK] The inverse bridge from displayed transport to owner-level reindexing. -/
@[stacks 0FLK]
theorem Realization.Map.cast_eq_reindex
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A]
    {K L : CochainComplex A ℤ} {f g : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (h : f = g)
    (m : Realization.Map F f S T) :
    DisplayedCategory.Hom.cast (displayedCategory F) h m =
      Realization.Map.reindex F h m := sorry

end CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Stupid
