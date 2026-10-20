/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DisplayedCategory.Fiber.Functor
public import ReasLib.CategoryTheory.DisplayedCategory.Fiber.NatTrans
public import ReasLib.CategoryTheory.DisplayedCategory.Functor.Category

/-!
# Evaluation of displayed functors on a fixed intrinsic fiber

For a fixed base functor and base object, displayed functors and identity-base displayed natural
transformations evaluate to an ordinary functor category.  This is the canonical entry point for
fiberwise naturality arguments.
-/

@[expose] public section

namespace CategoryTheory

universe v u v' u'

namespace DisplayedFunctor.Fiber

variable {C : Type u} [Category.{v} C]
variable {C' : Type u'} [Category.{v'} C']
variable {D : DisplayedCategory C} {E : DisplayedCategory C'} {F : C ⥤ C'}

/-- Evaluate displayed functors over `F` on the intrinsic fiber over `X`. -/
def evaluation (X : C) :
    DisplayedFunctor D E F ⥤
      (DisplayedCategory.Fiber D X ⥤ DisplayedCategory.Fiber E (F.obj X)) where
  obj Φ := DisplayedFunctor.fiberFunctor Φ X
  map η := DisplayedNatTrans.fiber η X
  map_id Φ := DisplayedNatTrans.fiber_id Φ X
  map_comp η θ := DisplayedNatTrans.fiber_comp η θ X

/-- Evaluation sends a displayed functor to its induced fiber functor. -/
@[simp]
theorem evaluation_obj (X : C) (Φ : DisplayedFunctor D E F) :
    (evaluation (D := D) (E := E) (F := F) X).obj Φ = DisplayedFunctor.fiberFunctor Φ X := rfl

/-- Evaluation sends an identity-base displayed transformation to its induced fiber map. -/
@[simp]
theorem evaluation_map (X : C) {Φ Ψ : DisplayedFunctor D E F}
    (η : Φ ⟶ Ψ) :
    (evaluation (D := D) (E := E) (F := F) X).map η = DisplayedNatTrans.fiber η X := rfl

end DisplayedFunctor.Fiber

end CategoryTheory
