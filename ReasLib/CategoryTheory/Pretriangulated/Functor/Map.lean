/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Triangulated.Functor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Vertex computations for mapped triangles

The triangle functor induced by a shift-compatible functor has objectwise vertex computations.  They
are kept in this small generic leaf so applications can use the equations without importing a
specialized derived-category construction.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Pretriangulated

noncomputable section

universe vC uC vD uD

namespace CategoryTheory.Functor

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable [HasShift C ℤ] [HasShift D ℤ]

/-- The first vertex of `F.mapTriangle.obj T` is the image of the first vertex of `T`. -/
@[stacks 014W "first vertex of a mapped triangle"]
theorem mapTriangle_obj₁_eq (F : C ⥤ D) [F.CommShift ℤ] (T : Triangle C) :
    (F.mapTriangle.obj T).obj₁ = F.obj T.obj₁ := sorry

/-- The second vertex of `F.mapTriangle.obj T` is the image of the second vertex of `T`. -/
@[stacks 014W "second vertex of a mapped triangle"]
theorem mapTriangle_obj₂_eq (F : C ⥤ D) [F.CommShift ℤ] (T : Triangle C) :
    (F.mapTriangle.obj T).obj₂ = F.obj T.obj₂ := sorry

/-- The third vertex of `F.mapTriangle.obj T` is the image of the third vertex of `T`. -/
@[stacks 014W "third vertex of a mapped triangle"]
theorem mapTriangle_obj₃_eq (F : C ⥤ D) [F.CommShift ℤ] (T : Triangle C) :
    (F.mapTriangle.obj T).obj₃ = F.obj T.obj₃ := sorry

end CategoryTheory.Functor

end
