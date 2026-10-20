/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Section.Construction

/-!
# Computations for neutral based-inertia sections

This leaf exposes the object, automorphism, and arrow readouts of the based
relative- and absolute-inertia identity sections.
-/

@[expose] public section

universe u v uX vX uY vY

namespace CategoryTheory
namespace BasedCategory

open BasedCategory BasedFunctor

variable {C : Type u} [Category.{v} C]
variable {X : BasedCategory.{vX, uX} C} {Y : BasedCategory.{vY, uY} C}

/-- The based relative-inertia identity section retains each source object. -/
@[simp, stacks 04Z3 "based relative-inertia identity-section object"]
theorem RelativeInertia.identitySection.obj (F : X ⥤ᵇ Y) (x : X.obj) :
    ((RelativeInertia.identitySection F).toFunctor.obj x).obj = x := sorry

/-- The based relative-inertia identity section selects the identity automorphism. -/
@[simp, stacks 04Z3 "based relative-inertia identity-section automorphism"]
theorem RelativeInertia.identitySection.aut (F : X ⥤ᵇ Y) (x : X.obj) :
    ((RelativeInertia.identitySection F).toFunctor.obj x).aut = 1 := sorry

/-- The based relative-inertia identity section retains each source arrow. -/
@[simp, stacks 04Z3 "based relative-inertia identity-section arrow"]
theorem RelativeInertia.identitySection.hom
    (F : X ⥤ᵇ Y) {x y : X.obj} (f : x ⟶ y) :
    CategoryTheory.RelativeInertia.hom
        ((RelativeInertia.identitySection F).toFunctor.map f) = f := sorry

/-- The based absolute-inertia identity section retains each source object. -/
@[simp, stacks 04Z3 "based absolute-inertia identity-section object"]
theorem Inertia.identitySection.obj (X : BasedCategory.{vX, uX} C) (x : X.obj) :
    ((Inertia.identitySection X).toFunctor.obj x).obj = x := sorry

/-- The based absolute-inertia identity section selects the identity automorphism. -/
@[simp, stacks 04Z3 "based absolute-inertia identity-section automorphism"]
theorem Inertia.identitySection.aut (X : BasedCategory.{vX, uX} C) (x : X.obj) :
    ((Inertia.identitySection X).toFunctor.obj x).aut = 1 := sorry

/-- The based absolute-inertia identity section retains each source arrow. -/
@[simp, stacks 04Z3 "based absolute-inertia identity-section arrow"]
theorem Inertia.identitySection.hom
    (X : BasedCategory.{vX, uX} C) {x y : X.obj} (f : x ⟶ y) :
    CategoryTheory.RelativeInertia.hom
        ((Inertia.identitySection X).toFunctor.map f) = f := sorry

end BasedCategory
end CategoryTheory
