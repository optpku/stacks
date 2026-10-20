/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Point.Category

/-!
# Maps on fibers of site points

This module exposes the component and generator formulas for the maps on
presheaf and sheaf fibers induced by a morphism of site points.  The formulas
are coefficient-independent, so they apply beyond the `Type`-valued case.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe u v w a b

namespace CategoryTheory.GrothendieckTopology.Point.Hom

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {A : Type a} [Category.{b} A] [HasColimitsOfSize.{w, w} A]
variable {p p' : GrothendieckTopology.Point.{w} J}

/-- The component of the sheaf-fiber map induced by a point morphism is the
component of its map on the underlying presheaf fibers. -/
theorem sheafFiber_app (f : p ⟶ p') (F : Sheaf J A) :
    f.sheafFiber.app F =
      f.presheafFiber.app ((sheafToPresheaf J A).obj F) := sorry

/-- A morphism of site points sends a canonical presheaf-fiber generator to
the generator indexed by the image under its underlying natural transformation. -/
@[simp, reassoc]
theorem toPresheafFiber_app
    (f : p ⟶ p') (P : Cᵒᵖ ⥤ A) (X : C) (x : p'.fiber.obj X) :
    p'.toPresheafFiber X x P ≫ f.presheafFiber.app P =
      p.toPresheafFiber X (f.hom.app X x) P := sorry

end CategoryTheory.GrothendieckTopology.Point.Hom
