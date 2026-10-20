/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.StrongTrans.Forget.Construction

import Mathlib.Tactic.CrossRefAttribute

/-!
# Computations for the forgetful strong transformation for based inertia

This leaf exposes the naturality components and the object component of the
forgetful strong transformation, including their underlying arrows.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory.BasedCategory.Inertia

open BasedCategory BasedFunctor
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace forget.naturalityIso

/-- The forward component of forgetful naturality is the explicit identity component. -/
@[simp, stacks 042H "based-inertia forgetful forward component computation"]
theorem hom.app
    {X Y : BasedCategory.{vS, max w vS} C} (F : X ⥤ᵇ Y)
    (A : (inertia X).obj) :
    (forget.naturalityIso F).hom.toNatTrans.app A = (component F A).hom := sorry

/-- The inverse component of forgetful naturality is the explicit identity component. -/
@[simp, stacks 042H "based-inertia forgetful inverse component computation"]
theorem inv.app
    {X Y : BasedCategory.{vS, max w vS} C} (F : X ⥤ᵇ Y)
    (A : (inertia X).obj) :
    (forget.naturalityIso F).inv.toNatTrans.app A = (component F A).inv := sorry

/-- The forward explicit forgetful comparison has the identity underlying arrow. -/
@[simp, stacks 042H "based-inertia forgetful forward underlying arrow"]
theorem component.hom.underlying
    {X Y : BasedCategory.{vS, max w vS} C} (F : X ⥤ᵇ Y)
    (A : (inertia X).obj) :
    (component F A).hom = 𝟙 (F.toFunctor.obj A.obj) := sorry

/-- The inverse explicit forgetful comparison has the identity underlying arrow. -/
@[simp, stacks 042H "based-inertia forgetful inverse underlying arrow"]
theorem component.inv.underlying
    {X Y : BasedCategory.{vS, max w vS} C} (F : X ⥤ᵇ Y)
    (A : (inertia X).obj) :
    (component F A).inv = 𝟙 (F.toFunctor.obj A.obj) := sorry

/-- The arrow underlying each forward forgetful naturality component is an identity. -/
@[simp, stacks 042H "based-inertia forgetful packaged forward underlying arrow"]
theorem hom.app.underlying
    {X Y : BasedCategory.{vS, max w vS} C} (F : X ⥤ᵇ Y)
    (A : (inertia X).obj) :
    (forget.naturalityIso F).hom.toNatTrans.app A =
      𝟙 (F.toFunctor.obj A.obj) := sorry

/-- The arrow underlying each inverse forgetful naturality component is an identity. -/
@[simp, stacks 042H "based-inertia forgetful packaged inverse underlying arrow"]
theorem inv.app.underlying
    {X Y : BasedCategory.{vS, max w vS} C} (F : X ⥤ᵇ Y)
    (A : (inertia X).obj) :
    (forget.naturalityIso F).inv.toNatTrans.app A =
      𝟙 (F.toFunctor.obj A.obj) := sorry

end forget.naturalityIso

namespace forget.strongTrans

/-- The component of the based-inertia forgetful transformation is the forgetful based functor. -/
@[simp, stacks 042H "based-inertia forgetful strong transformation component"]
theorem app (X : BasedCategory.{vS, max w vS} C) :
    (forget.strongTrans C).app X = forget X := sorry

/-- The naturality isomorphism of based-inertia forgetting is the explicit identity-component
comparison. -/
@[simp, stacks 042H "based-inertia forgetful strong transformation naturality"]
theorem naturality {X Y : BasedCategory.{vS, max w vS} C} (F : X ⟶ Y) :
    (forget.strongTrans C).naturality F =
      forget.naturalityIso F := sorry

end forget.strongTrans

end CategoryTheory.BasedCategory.Inertia
