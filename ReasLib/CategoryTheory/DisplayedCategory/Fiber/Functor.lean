/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DisplayedCategory.Fiber
public import ReasLib.CategoryTheory.DisplayedCategory.Functor

/-!
# Displayed functors on intrinsic fibers

A displayed functor over `F : C ⥤ C'` restricts at every base object `X` to a functor from the
intrinsic fiber over `X` to the intrinsic fiber over `F.obj X`.  Equality transport along
`F.map_id X` is confined to the morphism computation theorem.
-/

@[expose] public section

namespace CategoryTheory

universe v u v' u' v'' u''

namespace DisplayedFunctor

variable {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
variable {D : DisplayedCategory C} {E : DisplayedCategory C'} {F : C ⥤ C'}

namespace Fiber

/-- The displayed fiber map preserves identities after the canonical base-map transport. -/
theorem map_id (Phi : DisplayedFunctor D E F) (X : C)
    (x : DisplayedCategory.Fiber D X) :
    DisplayedCategory.Hom.cast E (F.map_id X)
        (Phi.map (DisplayedCategory.Fiber.id D X x)) =
      DisplayedCategory.Fiber.id E (F.obj X) (Phi.obj x) := sorry

/-- The displayed fiber map preserves composition after the canonical base-map transport. -/
theorem map_comp (Phi : DisplayedFunctor D E F) (X : C)
    {x y z : DisplayedCategory.Fiber D X} (f : x ⟶ y) (g : y ⟶ z) :
    DisplayedCategory.Hom.cast E (F.map_id X) (Phi.map (f ≫ g)) =
      DisplayedCategory.Fiber.comp
        (DisplayedCategory.Hom.cast E (F.map_id X) (Phi.map f))
        (DisplayedCategory.Hom.cast E (F.map_id X) (Phi.map g)) := sorry

end Fiber

/-- The functor on intrinsic fibers induced by a displayed functor. -/
def fiberFunctor (Phi : DisplayedFunctor D E F) (X : C) :
    DisplayedCategory.Fiber D X ⥤ DisplayedCategory.Fiber E (F.obj X) where
  obj x := Phi.obj x
  map f := DisplayedCategory.Hom.cast E (F.map_id X) (Phi.map f)
  map_id := DisplayedFunctor.Fiber.map_id Phi X
  map_comp := DisplayedFunctor.Fiber.map_comp Phi X

namespace fiberFunctor

/-- The object map of an induced fiber functor is the displayed object map. -/
@[simp]
theorem obj (Phi : DisplayedFunctor D E F) (X : C)
    (x : DisplayedCategory.Fiber D X) :
    (fiberFunctor Phi X).obj x = Phi.obj x := sorry

/-- The morphism map of an induced fiber functor is the displayed map transported along
`F.map_id`. -/
@[simp]
theorem map (Phi : DisplayedFunctor D E F) (X : C)
    {x y : DisplayedCategory.Fiber D X} (f : x ⟶ y) :
    (fiberFunctor Phi X).map f =
      DisplayedCategory.Hom.cast E (F.map_id X) (Phi.map f) := sorry

/-- The identity displayed functor induces the identity on every intrinsic fiber. -/
@[simp]
theorem id (D : DisplayedCategory C) (X : C) :
    fiberFunctor (DisplayedFunctor.id D) X = 𝟭 (DisplayedCategory.Fiber D X) := sorry

/-- Composition of displayed functors induces composition of their intrinsic-fiber functors. -/
@[simp]
theorem comp
    {C'' : Type u''} [Category.{v''} C''] {E' : DisplayedCategory C''} {G : C' ⥤ C''}
    (Phi : DisplayedFunctor D E F) (Psi : DisplayedFunctor E E' G) (X : C) :
    fiberFunctor (DisplayedFunctor.comp Phi Psi) X =
      fiberFunctor Phi X ⋙ fiberFunctor Psi (F.obj X) := sorry

/-- Restriction to an intrinsic fiber commutes with totalization and the fiber inclusions. -/
theorem comp_inclusion (Phi : DisplayedFunctor D E F) (X : C) :
    fiberFunctor Phi X ⋙ DisplayedCategory.Fiber.inclusion E (F.obj X) =
      DisplayedCategory.Fiber.inclusion D X ⋙ DisplayedFunctor.total Phi := sorry

end fiberFunctor

end DisplayedFunctor

end CategoryTheory
