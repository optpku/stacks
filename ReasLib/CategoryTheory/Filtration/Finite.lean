/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Category
public import ReasLib.CategoryTheory.Filtration.Exhaustive

/-!
# Finite Filtered Objects

This module packages the full subcategory of filtered objects whose filtrations have a top and a
bottom stage.  It is independent of any particular application of finite filtrations.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe v u

namespace CategoryTheory

namespace IndexedFiltration

variable {C : Type u} [Category.{v} C] [HasZeroObject C]
variable {I : Type*} [Preorder I] {A : C}

/-- A finite indexed filtration is separated: a subobject contained in every stage is contained
in its zero stage. -/
theorem isSeparated_of_isFinite (F : IndexedFiltration I A) (hfinite : IsFinite F) :
    IsSeparated F := sorry

/-- A finite indexed filtration is exhaustive: any subobject containing every stage contains its
top stage. -/
theorem isExhaustive_of_isFinite (F : IndexedFiltration I A) (hfinite : IsFinite F) :
    IsExhaustive F := sorry

end IndexedFiltration

namespace FilteredObject

variable {C : Type u} [Category.{v} C] [HasZeroObject C]

/-- A filtered object has a finite filtration when some stage is the whole object and some stage
is zero. -/
def IsFinite (I : FilteredObject C) : Prop :=
  IndexedFiltration.IsFinite I.filtration

end FilteredObject

namespace FilteredObject.Finite

/-- The category of finite filtered objects in `C`. -/
@[stacks 05RY]
abbrev category (C : Type u) [Category.{v} C] [HasZeroObject C] :=
  ObjectProperty.FullSubcategory
    (FilteredObject.IsFinite : ObjectProperty (FilteredObject C))

/-- The canonical notation for the full subcategory of finite filtered objects. -/
scoped notation "Filᶠ(" C ")" => FilteredObject.Finite.category C

/-- The inclusion of finite filtered objects into all filtered objects. -/
abbrev inclusion (C : Type u) [Category.{v} C] [HasZeroObject C] :
    category C ⥤ FilteredObject C :=
  ObjectProperty.ι (FilteredObject.IsFinite : ObjectProperty (FilteredObject C))

namespace Forget

/-- The forgetful functor from finite filtered objects to the ambient category.

This is the neutral owner of the construction. Complexes, homotopy categories, and derived
categories should all build on this functor rather than define a second restriction by hand.
-/

@[stacks 05RZ "finite filtered forgetful functor"]
abbrev functor (C : Type u) [Category.{v} C] [HasZeroObject C] :
    category C ⥤ C :=
  inclusion C ⋙ FilteredObject.forget

/-! The object and morphism formulas are kept beside the owner so downstream files can use them
without importing a complex-level module. -/

/-- The finite filtered forgetful functor returns the underlying ambient object. -/
@[stacks 05RZ "finite filtered forgetful functor", simp]
theorem obj {C : Type u} [Category.{v} C] [HasZeroObject C]
    (X : category C) : (functor C).obj X = X.obj.obj := sorry

/-- The finite filtered forgetful functor returns the underlying ambient morphism. -/
@[stacks 05RZ "finite filtered forgetful functor", simp]
theorem map {C : Type u} [Category.{v} C] [HasZeroObject C]
    {X Y : category C} (f : X ⟶ Y) : (functor C).map f = f.hom.hom := sorry

end Forget

end FilteredObject.Finite

end CategoryTheory
