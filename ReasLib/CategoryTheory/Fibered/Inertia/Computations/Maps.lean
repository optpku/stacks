/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Based.Construction

/-!
# Computations for neutral based-inertia structure maps

This leaf exposes the object and morphism readouts of the based relative- and
absolute-inertia forgetful functors.
-/

@[expose] public section

universe u v uX vX uY vY

namespace CategoryTheory
namespace BasedCategory

open BasedCategory BasedFunctor

variable {C : Type u} [Category.{v} C]
variable {X : BasedCategory.{vX, uX} C} {Y : BasedCategory.{vY, uY} C}

/-- The based relative-inertia forgetful map returns the underlying source object. -/
@[simp, stacks 042H "based relative-inertia forgetful object"]
theorem RelativeInertia.forget.obj (F : X ⥤ᵇ Y)
    (A : (relativeInertia F).obj) :
    (RelativeInertia.forget F).toFunctor.obj A = A.obj := sorry

/-- The based relative-inertia forgetful map returns the underlying source arrow. -/
@[simp, stacks 042H "based relative-inertia forgetful arrow"]
theorem RelativeInertia.forget.map (F : X ⥤ᵇ Y)
    {A B : (relativeInertia F).obj} (f : A ⟶ B) :
    (RelativeInertia.forget F).toFunctor.map f =
      CategoryTheory.RelativeInertia.hom f := sorry

/-- The based absolute-inertia forgetful map returns the underlying object. -/
@[simp, stacks 042H "based absolute-inertia forgetful object"]
theorem Inertia.forget.obj (X : BasedCategory.{vX, uX} C)
    (A : (inertia X).obj) :
    (Inertia.forget X).toFunctor.obj A = A.obj := sorry

/-- The based absolute-inertia forgetful map returns the underlying arrow. -/
@[simp, stacks 042H "based absolute-inertia forgetful arrow"]
theorem Inertia.forget.map (X : BasedCategory.{vX, uX} C)
    {A B : (inertia X).obj} (f : A ⟶ B) :
    (Inertia.forget X).toFunctor.map f =
      CategoryTheory.RelativeInertia.hom f := sorry

end BasedCategory
end CategoryTheory
