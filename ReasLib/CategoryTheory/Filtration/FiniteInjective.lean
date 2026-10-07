module

public import ReasLib.CategoryTheory.Filtration.Finite
public import ReasLib.CategoryTheory.Filtration.Injective
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite Filtered-Injective Objects

This module supplies the object property and full subcategory of finite filtered-injective
objects. Its canonical owner is `FilteredObject.Finite.FilteredInjective`; the underlying
condition remains the general `FilteredObject.IsFilteredInjective` predicate.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe v u

namespace CategoryTheory

namespace FilteredObject.Finite.FilteredInjective

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasZeroMorphisms C]
  [HasCokernels C]

/-- The object property on finite filtered objects consisting of filtered-injective objects. -/
@[stacks 015P]
abbrev property (C : Type u) [Category.{v} C] [HasZeroObject C] [HasZeroMorphisms C]
    [HasCokernels C] :
    ObjectProperty (FilteredObject.Finite.category C) :=
  fun I => FilteredObject.IsFilteredInjective I.obj

/-- The full subcategory of finite filtered objects that are filtered injective. -/
abbrev category (C : Type u) [Category.{v} C] [HasZeroObject C] [HasZeroMorphisms C]
    [HasCokernels C] :=
  ObjectProperty.FullSubcategory (property C)

namespace category

/-- An object of the filtered-injective full subcategory has its canonical filtered-injective
instance. -/
instance isFilteredInjective (I : category C) : FilteredObject.IsFilteredInjective I.obj.obj :=
  sorry

end category

namespace property

/-- Finite filtered-injective objects are invariant under isomorphism. -/
instance closedUnderIsomorphisms :
    (property C).IsClosedUnderIsomorphisms := sorry

end property

/-- The inclusion of finite filtered-injective objects into finite filtered objects. -/
abbrev inclusion (C : Type u) [Category.{v} C] [HasZeroObject C] [HasZeroMorphisms C]
    [HasCokernels C] :
    category C ⥤ FilteredObject.Finite.category C :=
  ObjectProperty.ι (property C)

/-- The forgetful functor from finite filtered-injective objects to the ambient category. -/
abbrev forget (C : Type u) [Category.{v} C] [HasZeroObject C] [HasZeroMorphisms C]
    [HasCokernels C] : category C ⥤ C :=
  inclusion C ⋙ FilteredObject.Finite.Forget.functor C

/-- Objectwise computation for the filtered-injective forgetful functor. -/
@[simp]
theorem forget_obj (I : category C) :
    (forget C).obj I = I.obj.obj.obj := sorry

/-- Morphismwise computation for the filtered-injective forgetful functor. -/
@[simp]
theorem forget_map {I J : category C} (f : I ⟶ J) :
    (forget C).map f = f.hom.hom.hom := sorry

end FilteredObject.Finite.FilteredInjective

end CategoryTheory
