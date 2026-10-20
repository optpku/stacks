/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Equalizers

/-!
# Contravariant images of forks

This file provides the cofork obtained by applying a contravariant functor to a fork.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory

namespace CategoryTheory.Limits.Fork

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/-- Applying a contravariant functor to a fork produces a cofork. -/
def mapOp {X Y : C} {f g : X ⟶ Y} (s : Fork f g) (F : Cᵒᵖ ⥤ D) :
    Cofork (F.map f.op) (F.map g.op) :=
  Cofork.ofCocone (F.mapCocone s.op)

/-- The point of the contravariant image of a fork is the image of its opposite point. -/
theorem mapOp_pt {X Y : C} {f g : X ⟶ Y} (s : Fork f g) (F : Cᵒᵖ ⥤ D) :
    (s.mapOp F).pt = F.obj (Opposite.op s.pt) := sorry

/-- The projection of the contravariant image is the image of the opposite fork inclusion. -/
theorem mapOp_π {X Y : C} {f g : X ⟶ Y} (s : Fork f g) (F : Cᵒᵖ ⥤ D) :
    (s.mapOp F).π = F.map s.ι.op := sorry

end CategoryTheory.Limits.Fork
