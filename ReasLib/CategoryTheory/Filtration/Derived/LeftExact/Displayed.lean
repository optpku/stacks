/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.LeftExact.SpectralSequence.Realization.Map.Category
public import ReasLib.CategoryTheory.DisplayedCategory.Total
public import ReasLib.CategoryTheory.DisplayedCategory.Transport

/-!
# Displayed support for finite right-derived realizations

The bounded-below finite filtered realization maps are exposed as a dependent hom family over
their source-complex morphisms.  The owner remains the finite right-derived spectral-sequence
namespace, while this leaf supplies the neutral displayed-category interface.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape
open CochainComplex.FilteredInjectivePlus

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Category.{v₂} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{w} B]

/-- `[stacks 015W]` The dependent category of finite right-derived realizations and their maps.
The base category is the bounded-below complex category of finite filtered objects. -/
@[stacks 015W]
def displayedCategory (T : A ⥤ₗ B) [EnoughInjectives A] :
    DisplayedCategory (CochainComplex.Plus (FilteredObject.Finite.category A)) where
  obj K := Realization T K
  Hom f S R := Realization.Map f S R
  id S := Realization.Map.id S
  comp m n := Realization.Map.comp m n
  id_comp := fun _ => sorry
  comp_id := fun _ => sorry
  assoc := fun _ _ _ => sorry

/-- `[stacks 015W]` The displayed-object family of finite right-derived realizations. -/
@[simp]
theorem displayedCategory_obj (T : A ⥤ₗ B) [EnoughInjectives A]
    (K : CochainComplex.Plus (FilteredObject.Finite.category A)) :
    (displayedCategory T).obj K = Realization T K := rfl

/-- `[stacks 015W]` The displayed hom family of finite right-derived realization maps. -/
@[simp]
theorem displayedCategory_hom (T : A ⥤ₗ B) [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    (S : Realization T K) (R : Realization T L) :
    (displayedCategory T).Hom f S R = Realization.Map f S R := rfl

/-- `[stacks 015W]` The identity operation of the displayed finite-realization category. -/
@[simp]
theorem displayedCategory_id (T : A ⥤ₗ B) [EnoughInjectives A]
    {K : CochainComplex.Plus (FilteredObject.Finite.category A)} (S : Realization T K) :
    (displayedCategory T).id S = Realization.Map.id S := rfl

/-- `[stacks 015W]` The composition operation of the displayed finite-realization category. -/
@[simp]
theorem displayedCategory_comp (T : A ⥤ₗ B) [EnoughInjectives A]
    {K L M : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L} {g : L ⟶ M}
    {S : Realization T K} {R : Realization T L} {U : Realization T M}
    (m : Realization.Map f S R) (n : Realization.Map g R U) :
    (displayedCategory T).comp m n = Realization.Map.comp m n := rfl

namespace Realization

/-- `[stacks 015W]` The total category of finite right-derived realizations.  An object consists of
a bounded-below finite filtered complex together with one of its realizations; a morphism retains
the underlying complex map and a compatible realization map. -/
@[stacks 015W "total category of finite right-derived realizations"]
abbrev Total (T : A ⥤ₗ B) [EnoughInjectives A] :=
  DisplayedCategory.Total (displayedCategory T)

namespace Total

/-- `[stacks 015W]` Forget a total finite right-derived realization to its bounded-below finite
filtered source complex. -/
@[stacks 015W "base of a total finite right-derived realization"]
abbrev forgetBase (T : A ⥤ₗ B) [EnoughInjectives A] :
    Realization.Total T ⥤ CochainComplex.Plus (FilteredObject.Finite.category A) :=
  DisplayedCategory.Total.forget (displayedCategory T)

/-- The base of a total finite right-derived realization is its stored finite filtered complex. -/
@[simp, stacks 015W "base of a total finite right-derived realization"]
theorem forgetBase_obj (T : A ⥤ₗ B) [EnoughInjectives A]
    (S : Realization.Total T) :
    (forgetBase T).obj S = S.base := sorry

/-- The base map of a total finite right-derived realization morphism is its stored base map. -/
@[simp, stacks 015W "base map of a total finite right-derived realization"]
theorem forgetBase_map (T : A ⥤ₗ B) [EnoughInjectives A]
    {S R : Realization.Total T} (m : S ⟶ R) :
    (forgetBase T).map m = m.base := sorry

end Total

end Realization

/-- `[stacks 015W]` Equality transport for finite right-derived realization maps agrees with the
canonical displayed transport. -/
@[simp, stacks 015W]
theorem Realization.Map.reindex_eq_cast
    {T : A ⥤ₗ B} [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f g : K ⟶ L}
    {S : Realization T K} {R : Realization T L} (h : f = g)
    (m : Realization.Map f S R) :
    Realization.Map.reindex h m = DisplayedCategory.Hom.cast (displayedCategory T) h m := sorry

/-- The generic displayed transport can be converted back to the owner-level finite-realization
reindexing. -/
@[stacks 015W "owner-level transport of finite right-derived realization maps"]
theorem Realization.Map.cast_eq_reindex
    {T : A ⥤ₗ B} [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f g : K ⟶ L}
    {S : Realization T K} {R : Realization T L} (h : f = g)
    (m : Realization.Map f S R) :
    DisplayedCategory.Hom.cast (displayedCategory T) h m =
      Realization.Map.reindex h m :=
  (Realization.Map.reindex_eq_cast h m).symm

end CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence
