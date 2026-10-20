module

public import ReasLib.CategoryTheory.DisplayedCategory.Total
public import ReasLib.CategoryTheory.DisplayedCategory.Transport

/-!
# Intrinsic fibers of displayed categories

The intrinsic fiber over `X` keeps exactly the displayed objects over `X` and the displayed
morphisms over `𝟙 X`.  The comparison with Mathlib's strict `Functor.Fiber` lives in the separate
`Fiber/Comparison` leaf.
-/

@[expose] public section

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]

namespace DisplayedCategory

/-- The intrinsic fiber of a displayed category over a base object.

This is a named type owner rather than an abbreviation, so its canonical category instance does
not become an instance on the underlying displayed-object type.  It remains definitionally equal
to `D.obj X`, preserving the direct displayed-object API. -/
def Fiber (D : DisplayedCategory C) (X : C) := D.obj X

namespace Fiber

/-- The identity morphism in the intrinsic displayed fiber. -/
def id (D : DisplayedCategory C) (X : C) (x : Fiber D X) :
    D.Hom (𝟙 X) x x :=
  D.id x

/-- Composition in the intrinsic displayed fiber, transported from
`𝟙 X ≫ 𝟙 X` to `𝟙 X`. -/
def comp {D : DisplayedCategory C} {X : C} {x y z : Fiber D X}
    (f : D.Hom (𝟙 X) x y) (g : D.Hom (𝟙 X) y z) : D.Hom (𝟙 X) x z :=
  DisplayedCategory.Hom.cast D (Category.comp_id (𝟙 X)) (D.comp f g)

/-- Left identity in the intrinsic displayed fiber. -/
theorem id_comp {D : DisplayedCategory C} {X : C} {x y : Fiber D X}
    (f : D.Hom (𝟙 X) x y) :
    comp (id D X x) f = f := sorry

/-- Right identity in the intrinsic displayed fiber. -/
theorem comp_id {D : DisplayedCategory C} {X : C} {x y : Fiber D X}
    (f : D.Hom (𝟙 X) x y) :
    comp f (id D X y) = f := sorry

/-- Associativity in the intrinsic displayed fiber. -/
theorem assoc {D : DisplayedCategory C} {X : C}
    {w x y z : Fiber D X}
    (f : D.Hom (𝟙 X) w x) (g : D.Hom (𝟙 X) x y) (h : D.Hom (𝟙 X) y z) :
    comp (comp f g) h = comp f (comp g h) := sorry

/-- The category structure on the intrinsic displayed fiber. -/
instance category (D : DisplayedCategory C) (X : C) : Category (Fiber D X) where
  Hom x y := D.Hom (𝟙 X) x y
  id x := id D X x
  comp f g := comp f g
  id_comp := id_comp
  comp_id := comp_id
  assoc := assoc

/-- The identity morphism computes to the displayed identity. -/
@[simp]
theorem id_apply (D : DisplayedCategory C) (X : C) (x : Fiber D X) :
    (𝟙 x : x ⟶ x) = D.id x := sorry

/-- Composition computes to the transported displayed composite. -/
@[simp]
theorem comp_apply {D : DisplayedCategory C} {X : C}
    {x y z : Fiber D X} (f : x ⟶ y) (g : y ⟶ z) :
    f ≫ g =
      DisplayedCategory.Hom.cast D (Category.comp_id (𝟙 X)) (D.comp f g) := sorry

/-- A fiber morphism regarded as a total-category morphism over the identity of `X`. -/
def lift {D : DisplayedCategory C} {X : C} {x y : Fiber D X} (f : x ⟶ y) :
    (⟨X, x⟩ : DisplayedCategory.Total D) ⟶ ⟨X, y⟩ :=
  { base := 𝟙 X, displayed := f }

/-- An intrinsic-fiber morphism has a canonical hom-lift certificate after inclusion into the
total category. -/
instance lift_isHomLift {D : DisplayedCategory C} {X : C}
    {x y : Fiber D X} (f : x ⟶ y) :
    (DisplayedCategory.Total.forget D).IsHomLift (𝟙 X) (lift f) := sorry

/-- The base component of a lifted intrinsic-fiber morphism. -/
@[simp]
theorem lift_base {D : DisplayedCategory C} {X : C} {x y : Fiber D X} (f : x ⟶ y) :
    (lift f).base = 𝟙 X := sorry

/-- The displayed component of a lifted intrinsic-fiber morphism. -/
@[simp]
theorem lift_displayed {D : DisplayedCategory C} {X : C} {x y : Fiber D X} (f : x ⟶ y) :
    (lift f).displayed = f := sorry

/-- The identity computation required by the displayed-fiber inclusion. -/
theorem inclusion_map_id (D : DisplayedCategory C) (X : C) (x : Fiber D X) :
    lift (𝟙 x) = 𝟙 (⟨X, x⟩ : DisplayedCategory.Total D) := sorry

/-- The composition computation required by the displayed-fiber inclusion. -/
theorem inclusion_map_comp {D : DisplayedCategory C} (X : C)
    {x y z : Fiber D X} (f : x ⟶ y) (g : y ⟶ z) :
    lift (f ≫ g) = lift f ≫ lift g := sorry

/-- The inclusion of the intrinsic displayed fiber into the total category. -/
def inclusion (D : DisplayedCategory C) (X : C) :
    Fiber D X ⥤ DisplayedCategory.Total D where
  obj x := ⟨X, x⟩
  map f := lift f
  map_id := fun x => inclusion_map_id D X x
  map_comp := fun f g => inclusion_map_comp X f g

/-- The object computation of the displayed-fiber inclusion. -/
@[simp]
theorem inclusion_obj (D : DisplayedCategory C) (X : C) (x : Fiber D X) :
    (inclusion D X).obj x = (⟨X, x⟩ : DisplayedCategory.Total D) := sorry

/-- The morphism computation of the displayed-fiber inclusion. -/
@[simp]
theorem inclusion_map {D : DisplayedCategory C} (X : C)
    {x y : Fiber D X} (f : x ⟶ y) :
    (inclusion D X).map f =
      lift f := sorry

/-- The base component of an intrinsic-fiber inclusion morphism. -/
@[simp]
theorem inclusion_map_base {D : DisplayedCategory C} (X : C)
    {x y : Fiber D X} (f : x ⟶ y) :
    ((inclusion D X).map f).base = 𝟙 X := sorry

/-- The displayed component of an intrinsic-fiber inclusion morphism. -/
@[simp]
theorem inclusion_map_displayed {D : DisplayedCategory C} (X : C)
    {x y : Fiber D X} (f : x ⟶ y) :
    ((inclusion D X).map f).displayed = f := sorry

/-- The intrinsic-fiber inclusion is faithful on morphisms. -/
@[ext]
theorem hom_ext {D : DisplayedCategory C} {X : C} {x y : Fiber D X}
    {f g : x ⟶ y} (h : (inclusion D X).map f = (inclusion D X).map g) :
    f = g := sorry

/-- Every morphism in an intrinsic fiber is mapped by its inclusion over the identity of the
base object. -/
instance inclusion_isHomLift {D : DisplayedCategory C} {X : C}
    {x y : Fiber D X} (f : x ⟶ y) :
    (DisplayedCategory.Total.forget D).IsHomLift (𝟙 X) ((inclusion D X).map f) := sorry

/-- The projection of the displayed-fiber inclusion is the constant functor at `X`. -/
theorem inclusion_comp_forget (D : DisplayedCategory C) (X : C) :
    inclusion D X ⋙ DisplayedCategory.Total.forget D =
      (Functor.const (Fiber D X)).obj X := sorry

end Fiber

end DisplayedCategory

end CategoryTheory
