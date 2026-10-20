/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DisplayedCategory.Structure
public import ReasLib.CategoryTheory.DisplayedCategory.Transport
public import Mathlib.CategoryTheory.FiberedCategory.HomLift

/-!
# Total categories of displayed categories

This file assembles the dependent objects and displayed morphisms of a
`DisplayedCategory` into an ordinary category.  The projection and the bridge to
`BasedCategory` are kept here so that downstream constructions can use the existing
over-a-base API without unfolding dependent transports.
-/

@[expose] public section

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]

namespace DisplayedCategory

/-- The total category of a displayed category.  An object consists of a base object and a
displayed object over it. -/
@[stacks 015N "total category of a displayed category"]
structure Total (D : DisplayedCategory C) where
  /-- The base object of a total object. -/
  base : C
  /-- The displayed object over `base`. -/
  obj : D.obj base

namespace Total

/-- A morphism in the total category consists of a base morphism and a displayed morphism over it.
-/
@[stacks 015N "morphisms in the total category of a displayed category"]
structure Hom (D : DisplayedCategory C) (X Y : Total D) where
  /-- The underlying morphism in the base category. -/
  base : X.base ⟶ Y.base
  /-- The displayed morphism lying over `base`. -/
  displayed : D.Hom base X.obj Y.obj

/-- The displayed component of a total morphism, exposed under the conventional `map` view.

This projection belongs to the total-category owner itself, so clients importing only the basic
total category do not need to depend on the transport leaf. -/
@[stacks 015N "displayed map view of a total morphism"]
abbrev Hom.map {D : DisplayedCategory C} {X Y : Total D} (f : Hom D X Y) := f.displayed

/-- Dependent extensionality for total objects. -/
@[ext (iff := false)]
theorem ext {D : DisplayedCategory C} {X Y : Total D}
    (h_base : X.base = Y.base)
    (h_obj : _root_.CategoryTheory.DisplayedCategory.Obj.cast D h_base X.obj = Y.obj) :
    X = Y := sorry

/-- With a chosen equality of base objects, total-object equality is equivalent to equality of the
displayed objects after canonical transport. -/
@[simp]
theorem ext_iff_of_base {D : DisplayedCategory C} {X Y : Total D}
    (h_base : X.base = Y.base) :
    X = Y ↔ _root_.CategoryTheory.DisplayedCategory.Obj.cast D h_base X.obj = Y.obj := sorry

/-- Dependent extensionality for total morphisms. -/
@[ext (iff := false)]
theorem Hom.ext {D : DisplayedCategory C} {X Y : Total D}
    {f g : Hom D X Y} (h_base : f.base = g.base)
    (h_displayed : _root_.CategoryTheory.DisplayedCategory.Hom.cast D h_base f.displayed = g.displayed) :
    f = g := sorry

/-- With a chosen equality of base morphisms, total-morphism equality is equivalent to equality of
the displayed components after canonical transport. -/
@[simp]
theorem Hom.ext_iff_of_base {D : DisplayedCategory C} {X Y : Total D}
    {f g : Hom D X Y} (h_base : f.base = g.base) :
    f = g ↔ _root_.CategoryTheory.DisplayedCategory.Hom.cast D h_base f.displayed = g.displayed := sorry

/-- The identity morphism in the total category. -/
def id (D : DisplayedCategory C) (X : Total D) : Hom D X X where
  base := 𝟙 X.base
  displayed := D.id X.obj

/-- Composition of total morphisms. -/
def comp {D : DisplayedCategory C} {X Y Z : Total D}
    (f : Hom D X Y) (g : Hom D Y Z) : Hom D X Z where
  base := f.base ≫ g.base
  displayed := D.comp f.displayed g.displayed

/-- The explicitly constructed identity is a left identity for total morphisms. -/
theorem id_comp {D : DisplayedCategory C} {X Y : Total D} (f : Hom D X Y) :
    comp (id D X) f = f := sorry

/-- The explicitly constructed identity is a right identity for total morphisms. -/
theorem comp_id {D : DisplayedCategory C} {X Y : Total D} (f : Hom D X Y) :
    comp f (id D Y) = f := sorry

/-- Explicit composition of total morphisms is associative. -/
theorem assoc {D : DisplayedCategory C} {W X Y Z : Total D}
    (f : Hom D W X) (g : Hom D X Y) (h : Hom D Y Z) :
    comp (comp f g) h = comp f (comp g h) := sorry

/-- The displayed category totalization is an ordinary category. -/
@[stacks 015N "category structure on displayed-category totals"]
instance category (D : DisplayedCategory C) : Category (Total D) where
  Hom X Y := Hom D X Y
  id X := id D X
  comp f g := comp f g
  id_comp := id_comp
  comp_id := comp_id
  assoc := assoc

/-- The base component of the identity total morphism. -/
@[simp]
theorem id_base (D : DisplayedCategory C) (X : Total D) :
    (𝟙 X : X ⟶ X).base = 𝟙 X.base := sorry

/-- The displayed component of the identity total morphism. -/
@[simp]
theorem id_displayed (D : DisplayedCategory C) (X : Total D) :
    (𝟙 X : X ⟶ X).displayed = D.id X.obj := sorry

/-- The base component of a composite total morphism. -/
@[simp]
theorem comp_base {D : DisplayedCategory C} {X Y Z : Total D}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).base = f.base ≫ g.base := sorry

/-- The displayed component of a composite total morphism. -/
@[simp]
theorem comp_displayed {D : DisplayedCategory C} {X Y Z : Total D}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).displayed = D.comp f.displayed g.displayed := sorry

/-- The projection from the total category to the base category. -/
@[stacks 015N "base projection of a displayed-category total"]
def forget (D : DisplayedCategory C) : Total D ⥤ C where
  obj X := X.base
  map f := f.base
  map_id := fun X => id_base D X
  map_comp := fun f g => comp_base f g

/-- The object component of the total-category projection. -/
@[simp]
theorem forget_obj (D : DisplayedCategory C) (X : Total D) :
    (forget D).obj X = X.base := sorry

/-- The morphism component of the total-category projection. -/
@[simp]
theorem forget_map {D : DisplayedCategory C} {X Y : Total D} (f : X ⟶ Y) :
    (forget D).map f = f.base := sorry

/-- Every morphism in the total category canonically lies over its stored base morphism. -/
@[stacks 015N "canonical hom-lift for a displayed-category total"]
instance hom_isHomLift {D : DisplayedCategory C} {X Y : Total D} (f : X ⟶ Y) :
    (forget D).IsHomLift f.base f := sorry

/-- A total morphism can be used as a lift of any propositionally equal base arrow.

This explicit certificate is useful when the base arrow is obtained through a comparison or a
transport rather than by projection, and avoids downstream `letI` reconstruction. -/
theorem isHomLift_of_eq {D : DisplayedCategory C} {X Y : Total D}
    {g : X.base ⟶ Y.base} (f : X ⟶ Y) (h : g = f.base) :
    (forget D).IsHomLift g f := sorry

/-- A total morphism lies over a base morphism exactly when that morphism is its stored base
component. -/
@[simp]
theorem isHomLift_iff {D : DisplayedCategory C} {X Y : Total D}
    (g : X.base ⟶ Y.base) (f : X ⟶ Y) :
    (forget D).IsHomLift g f ↔ g = f.base := sorry

end Total

end DisplayedCategory

end CategoryTheory
